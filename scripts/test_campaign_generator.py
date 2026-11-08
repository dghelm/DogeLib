"""Semantic reach and signer checks for stage 2 of design record 0009."""

import argparse
import copy
import json
import pathlib
import subprocess
import sys
import tempfile

import campaign
from campaign_generator import plans, signing_requests
from compare_core import read_compact_size


def context(request):
    """Read wire fields and the unlocking stack, independently of generator plans."""
    tx = bytes.fromhex(request['tx_hex'])
    inputs, pos = read_compact_size(tx, 4)
    sequences, unlocking = [], b''
    for i in range(inputs):
        pos += 36
        length, pos = read_compact_size(tx, pos)
        if i == request['input_index']:
            unlocking = tx[pos:pos + length]
        pos += length
        sequences.append(int.from_bytes(tx[pos:pos + 4], 'little'))
        pos += 4
    outputs, _ = read_compact_size(tx, pos)
    stack, cursor = [], 0
    while cursor < len(unlocking):
        op = unlocking[cursor]
        cursor += 1
        if op <= 75:
            size = op
        elif op == 76:
            size = unlocking[cursor]
            cursor += 1
        elif 81 <= op <= 96:
            stack.append(bytes([op - 80]))
            continue
        else:
            break
        stack.append(unlocking[cursor:cursor + size])
        cursor += size
    return dict(inputs=inputs, outputs=outputs, sequences=sequences, stack=stack,
                lock_time=int.from_bytes(tx[-4:], 'little'))


def mutate_response(mode, request, response):
    """Plant M1–M6 using only semantic request fields and the actual response."""
    if request['op'] not in ('sighash.legacy', 'script.verify_legacy'):
        return None
    c = context(request)
    n, op = request['input_index'], request['op']
    result = response.get('ok', {})
    if mode == 'M1' and op == 'script.verify_legacy' and c['inputs'] >= 3:
        sigs = c['stack'][:-2]
        if any(sig and sig[-1] == 0x82 for sig in sigs) and result.get('result') == 'rejected':
            response['ok'] = dict(result='accepted', script_error='OK')
    if mode == 'M2' and op == 'sighash.legacy' and request['hash_type'] & 31 == 3 and n > 0:
        digest = bytearray.fromhex(result['digest_hex'])
        digest[0] ^= 1
        result['digest_hex'] = digest.hex()
    if mode == 'M3' and op == 'script.verify_legacy' and c['lock_time'] == 500000000:
        selector = c['stack'][-2] if len(c['stack']) >= 2 else b'\x01'
        truth = any(b and not (i == len(selector) - 1 and b == 128) for i, b in enumerate(selector))
        if not truth:
            response['ok'] = dict(result='accepted', script_error='OK')
    if mode == 'M4' and any(seq == 0xffffffff for i, seq in enumerate(c['sequences']) if i != n):
        return 'crash'
    if mode == 'M5' and c['outputs'] >= 5:
        return 'timeout'
    if mode == 'M6' and op == 'sighash.legacy' and result.get('plan') == 'fixed_digest':
        result['digest_hex'] = '00' * 32
    return None


def stage2(args, wrapper, check):
    """Require discovery by the seeded stream and replay every mutant detection."""
    root = campaign.ROOT
    signer = str(pathlib.Path(args.signer or pathlib.Path(args.harness).with_name('core-signer')).resolve())
    base = root / 'build/campaign'
    detection = []
    checks = 0
    from campaign_generator import mutated
    moves, single_outputs = set(), set()
    for plan in plans(20261108, 2000):
        for mutation in plan['mutations']:
            if mutation['field'] == 'position':
                after = mutated(plan)
                moves.add((plan['n'], after['n']))
                check(after['tx']['inputs'][after['n']] == plan['tx']['inputs'][plan['n']],
                      'position mutation lost the signed input')
            if mutation['field'] == 'other_output':
                target = mutation.get('index', 0 if plan['n'] else 1)
                for h in plan['hash_types']:
                    if h & 31 == 3:
                        single_outputs.add((h, plan['mode'], target > plan['n']))
    check(moves == {(n, target) for n in range(3) for target in range(3) if n != target}, moves)
    check(single_outputs == {(h, mode, after) for h in (3, 131)
                             for mode in ('preserve', 'commitment') for after in (False, True)}, single_outputs)
    print('ok boundaries: both SINGLE output directions and all six position moves')
    checks += 1
    with tempfile.TemporaryDirectory(prefix='stage2-', dir=base) as tmp:
        tmp = pathlib.Path(tmp)
        opts = argparse.Namespace(campaign='generated', signer=signer, seed=20261108, cases=2000,
                                  seconds=120, timeout=3, batch_size=16, inputs=['generated'],
                                  oracle=args.oracle, harness=args.harness, stop_after_failure=True)
        for mode, side, kind in (('M1', 'core', 'verdict'), ('M2', 'lean', 'digest'),
                                 ('M3', 'core', 'verdict'), ('M4', 'core', 'crash'),
                                 ('M5', 'lean', 'timeout'), ('M6', 'core', 'digest')):
            local = copy.deepcopy(opts)
            local.output = str(tmp / mode)
            setattr(local, 'oracle' if side == 'lean' else 'harness',
                    wrapper(tmp / (mode + '-wrapper'), mode, args.oracle if side == 'lean' else args.harness))
            summary = campaign.run_campaign(local)
            records = [json.loads(pathlib.Path(p).read_text()) for p in summary['saved']]
            found = [(p, r) for p, r in zip(summary['saved'], records) if r['class'] == kind]
            if mode in ('M4', 'M5'):
                def triggered(record):
                    for request in record['requests']:
                        c = context(request)
                        if mode == 'M5' and c['outputs'] >= 5:
                            return True
                        if mode == 'M4' and any(seq == 0xffffffff for i, seq in enumerate(c['sequences'])
                                                if i != request['input_index']):
                            return True
                    return False

                found = [(p, r) for p, r in found if triggered(r)]
            check(bool(found), f'{mode} survived its 2000-case, 120-second budget')
            path, record = min(found, key=lambda item: item[1]['case_index'])
            replay = subprocess.run([sys.executable, '-I', str(root / 'scripts/campaign.py'), 'replay',
                                     path, local.oracle, local.harness], capture_output=True, text=True)
            check(replay.returncode == 0, replay.stderr + replay.stdout)
            clean = subprocess.run([sys.executable, '-I', str(root / 'scripts/campaign.py'), 'replay',
                                    path, args.oracle, args.harness], capture_output=True, text=True)
            check(clean.returncode == 1, clean.stderr + clean.stdout)
            detection.append(dict(mutant=mode, seed=local.seed, case_index=record['case_index'],
                                  outcome=kind, replay=True, clean_replay=False,
                                  budget=dict(cases=local.cases, seconds=local.seconds),
                                  completed=summary['completed'], elapsed_seconds=summary['elapsed_seconds']))
            print(f"ok {mode}: detected {kind} at case {record['case_index']}, replay reproduced")
            checks += 1
        local = copy.deepcopy(opts)
        local.output = str(tmp / 'q6-only')
        local.oracle = wrapper(tmp / 'q6-only-lean', 'q6-after', args.oracle)
        plan = next(p for p in plans(20261108, 2000)
                    if p['mode'] == 'preserve' and p['boundary'] == 'field')
        summary = campaign.run_campaign(local, [dict(plan=plan)])
        record = json.loads(pathlib.Path(summary['saved'][0]).read_text())
        check(record['class'] == 'digest' and record['failing_side'] == 'undetermined', record)
        check(record['property'] == 'Q6', record)
        check(record['expected']['relation'] == 'compare_core.compare agreement', record)
        check('Q6' in record['expected']['text'], record)
        print('ok Q6-only: generated disagreement saves the comparison property and expectation')
        checks += 1
        from campaign_generator import property_result
        plan = next(p for p in plans(20261108, 2000)
                    if p['mode'] == 'commitment' and p['boundary'] == 'field'
                    and p['mutations'][0]['field'] == 'version')
        built, _, _ = campaign.prepare_generated(opts, [dict(plan=plan, case_index=0)], 10)
        case = built[0]
        runs = {side: campaign.execute(program, case['requests'], 10)
                for side, program in (('lean', args.oracle), ('core', args.harness))}
        for run in runs.values():
            run['responses'][-1]['ok'] = dict(result='unsupported', reason='flags', bits=64)
        check(property_result(case, runs) is None, 'unsupported spend became a verdict failure')
        for field in ('digest_hex', 'preimage_hex'):
            faulty = copy.deepcopy(runs)
            faulty['lean']['responses'][1]['ok'][field] = faulty['lean']['responses'][0]['ok'][field]
            result = property_result(case, faulty)
            check(result and result[0] == 'digest' and result[1] == 'lean' and result[4] == 'Q4', result)
        print('ok unsupported: digest and preimage checks survive the excluded spend')
        checks += 1
        requests = [r for i, plan in enumerate(plans(20261108, 64))
                    for r in signing_requests(plan, f'generated-{i}')]
        first = campaign.execute(signer, requests, 10, ['--sign'])
        second = campaign.execute(signer, requests, 10, ['--sign'])
        check(first.get('responses') == second.get('responses') and 'error' not in first,
              'signer determinism failed')
        check(all('ok' in r for r in first['responses']), 'signer refused a generated domain member')
        print('ok signer: repeated signing requests give identical responses')
        checks += 1
        # A real structured refusal, saved by the normal run path, must replay.
        from unittest.mock import patch
        original = campaign.prepare_generated

        def invalid_key(options, batch, timeout):
            from campaign_generator import signing_requests as real_requests

            def bad_ids(plan, prefix):
                return [dict(r, key_ids=[5]) for r in real_requests(plan, prefix)]

            with patch('campaign_generator.signing_requests', side_effect=bad_ids):
                return original(options, batch, timeout)

        local = copy.deepcopy(opts)
        local.output = str(tmp / 'refusal')
        local.cases = 1
        raw = [dict(plan=next(plans(20261108, 1)))]
        with patch.object(campaign, 'prepare_generated', side_effect=invalid_key):
            summary = campaign.run_campaign(local, raw)
        check(summary['counts']['refusal'] == 1, 'signer refusal was not saved')
        replay = subprocess.run([sys.executable, '-I', str(root / 'scripts/campaign.py'), 'replay',
                                 '--signer', signer, summary['saved'][0], args.oracle, args.harness],
                                capture_output=True, text=True)
        check(replay.returncode == 0, replay.stderr + replay.stdout)
        print('ok signer: saved structured refusal reproduces with replay --signer')
        checks += 1
        local.signer = wrapper(tmp / 'malformed-signer', 'signer-shape', signer)
        local.output = str(tmp / 'malformed-signer-run')
        summary = campaign.run_campaign(local, [dict(plan=next(plans(20261108, 1)))])
        check(summary['counts']['crash'] == 1, 'malformed signer response was not saved')
        replay = subprocess.run([sys.executable, '-I', str(root / 'scripts/campaign.py'), 'replay',
                                 '--signer', local.signer, summary['saved'][0], args.oracle, args.harness],
                                capture_output=True, text=True)
        check(replay.returncode == 0, replay.stderr + replay.stdout)
        print('ok signer: malformed response reproduces with replay --signer')
        checks += 1
    path = base / 'mutant-detection.json'
    path.write_text(json.dumps(detection, indent=2) + '\n')
    return checks
