"""Stage 3 of design record 0009: the planted proposal search and the reducer."""

import argparse
import json
import pathlib
import subprocess
import sys
import tempfile

import campaign
from campaign_proposal import SPACE_SIZE, ALPHABET, LOCK_TIMES, SEQUENCES, parse_script, script_case, script_plan
from campaign_reduce import condition, reduce_failure
from test_campaign_generator import context

# Scripts of one and two instructions, in every context, come first in the enumeration.
SHORT = sum(len(ALPHABET) ** n for n in (1, 2)) * len(LOCK_TIMES) * len(SEQUENCES)
UP_TO_THREE = SHORT + len(ALPHABET) ** 3 * len(LOCK_TIMES) * len(SEQUENCES)


def trigger(mode, request):
    """The semantic trigger of each mutant of section 8.2, read from one request alone."""
    if request['op'] not in ('sighash.legacy', 'script.verify_legacy'):
        return False
    c = context(request)
    n = request['input_index']
    if mode == 'M1':
        return (request['op'] == 'script.verify_legacy' and c['inputs'] >= 3 and
                any(sig and sig[-1] == 0x82 for sig in c['stack'][:-2]))
    if mode == 'M2':
        return request['op'] == 'sighash.legacy' and request['hash_type'] & 31 == 3 and n > 0
    if mode == 'M3':
        selector = c['stack'][-2] if len(c['stack']) >= 2 else b'\x01'
        truth = any(b and not (i == len(selector) - 1 and b == 128) for i, b in enumerate(selector))
        return (request['op'] == 'script.verify_legacy' and request['flags'] & 512 and not truth and
                c['lock_time'] == 500000000 and c['sequences'][n] != 0xffffffff)
    if mode == 'M4':
        return any(seq == 0xffffffff for i, seq in enumerate(c['sequences']) if i != n)
    if mode == 'M5':
        return c['outputs'] >= 5
    if mode == 'M6':
        return request['op'] == 'sighash.legacy' and request['hash_type'] & 31 == 3 and n >= c['outputs']
    raise ValueError(mode)


def shape(plan):
    """Sizes that a report can compare before and after a reduction."""
    return dict(inputs=len(plan['tx']['inputs']), outputs=len(plan['tx']['outputs']),
                mutations=len(plan['mutations']), signature_mutation=plan['signature_mutation'],
                n=plan['n'], flags=plan['flags'], hash_types=plan['hash_types'])


def check_reduction(mode, path, local, check):
    """Reduce one saved mutant detection, and require its trigger, condition and replay to survive."""
    original = json.loads(pathlib.Path(path).read_text())
    target, reduced = reduce_failure(path, local.oracle, local.harness, local.signer)
    check(condition(reduced) == condition(original), f'{mode}: reduction changed the failure condition')
    check(reduced['reduced_from'] == pathlib.Path(path).name, f'{mode}: reduced_from is wrong')
    label = reduced['reduction']['label']
    check(label in ('minimal', 'budget'), f'{mode}: unknown label {label}')
    check(any(trigger(mode, r) for r in reduced['requests']), f'{mode}: reduction lost the trigger')
    replay = subprocess.run([sys.executable, '-I', str(campaign.ROOT / 'scripts/campaign.py'), 'replay',
                             str(target), local.oracle, local.harness], capture_output=True, text=True)
    check(replay.returncode == 0, f'{mode}: reduced failure does not replay: {replay.stdout}{replay.stderr}')
    result = dict(mutant=mode, label=label, candidates=reduced['reduction']['candidates'],
                  changes=len(reduced['reduction']['steps']),
                  before=shape(original['plan']['inputs'][0]['plan']),
                  after=shape(reduced['plan']['inputs'][0]['plan']))
    print(f"ok {mode}: reduced with label {label} after {result['candidates']} candidates, "
          f"trigger kept, replay reproduced")
    return result


def instructions(record):
    """The script plan of a saved proposal failure."""
    return record['plan']['inputs'][0]['plan']


def stage3(args, check):
    """Run the blind search on both variants and reduce the five-instruction seed."""
    replay_program = str(pathlib.Path(args.proposal_replay).resolve())
    base = campaign.ROOT / 'build/campaign'
    checks = 0
    with tempfile.TemporaryDirectory(prefix='stage3-', dir=base) as tmp:
        tmp = pathlib.Path(tmp)
        options = argparse.Namespace(campaign='proposal', variant='faulty', seed=0, cases=UP_TO_THREE,
                                     seconds=600, timeout=60, batch_size=2000, inputs=[],
                                     oracle=args.oracle, harness=replay_program, output=str(tmp / 'faulty'))
        summary = campaign.run_campaign(options)
        check(summary['completed'] == UP_TO_THREE and not summary['exhausted'], summary)
        records = [json.loads(pathlib.Path(p).read_text()) for p in summary['saved']]
        check(records, 'the blind search found no violation of the faulty rule')
        check(all(condition(r) == ('RestrictsAcceptance', 'verdict', 'revised') for r in records),
              'a proposal search failure is not a revised-side verdict')
        check(all(len(instructions(r)['instructions']) == 3 for r in records),
              'the blind search found a violation that does not have three instructions')
        check(min(r['case_index'] for r in records) >= SHORT, 'a violation lies among the short scripts')
        check(any(instructions(r)['instructions'] == ['51', '00', 'b3'] and instructions(r)['tx']['lock_time'] == 2
                  and instructions(r)['tx']['inputs'][0]['sequence'] == 0xfffffffe for r in records),
              'the search missed 51 00 b3 at lock time 2')
        first = min(zip(summary['saved'], records), key=lambda item: item[1]['case_index'])
        replay = subprocess.run([sys.executable, '-I', str(campaign.ROOT / 'scripts/campaign.py'), 'replay',
                                 first[0], args.oracle, replay_program], capture_output=True, text=True)
        check(replay.returncode == 0, replay.stdout + replay.stderr)
        print(f"ok proposal faulty: {len(records)} violations, all of three instructions, "
              f"first at case {first[1]['case_index']}, none in the {SHORT} shorter cases, replay reproduced")
        checks += 1
        options.variant, options.cases, options.output = 'corrected', SPACE_SIZE, str(tmp / 'corrected')
        summary = campaign.run_campaign(options)
        check(summary['completed'] == SPACE_SIZE and not summary['exhausted'], summary)
        check(summary['failures'] == 0 and not summary['saved'], 'the corrected variant has a violation')
        check(all(summary['counts'][k] == 0 for k in campaign.CLASSES), summary['counts'])
        print(f'ok proposal corrected: no violation in all {SPACE_SIZE} cases of one to five instructions')
        checks += 1
        options.variant, options.cases, options.output = 'faulty', 1, str(tmp / 'seed')
        seed = script_case(script_plan(parse_script('5152b35187'), 2, 0xfffffffe), 0)
        summary = campaign.run_campaign(options, [seed])
        check(len(summary['saved']) == 1, 'the five-instruction seed is not a violation')
        target, reduced = reduce_failure(summary['saved'][0], args.oracle, replay_program)
        plan = instructions(reduced)
        check(reduced['reduction']['label'] == 'minimal', reduced['reduction'])
        check(len(plan['instructions']) == 3, plan)
        check(condition(reduced) == ('RestrictsAcceptance', 'verdict', 'revised'), 'the seed changed condition')
        replay = subprocess.run([sys.executable, '-I', str(campaign.ROOT / 'scripts/campaign.py'), 'replay',
                                 str(target), args.oracle, replay_program], capture_output=True, text=True)
        check(replay.returncode == 0, replay.stdout + replay.stderr)
        trace = '; '.join(f"step {s['step']}: {s['change']}" for s in reduced['reduction']['steps'])
        print(f"ok reducer: 51 52 b3 51 87 becomes {' '.join(plan['instructions'])} at lock time "
              f"{plan['tx']['lock_time']}, label minimal after {reduced['reduction']['candidates']} candidates ({trace})")
        checks += 1
    return checks
