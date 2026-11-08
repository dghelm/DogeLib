"""Run fixed-input agreement campaigns and replay complete saved failures."""

import argparse
import hashlib
import json
import math
import os
import pathlib
import platform
import random
import shlex
import signal
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
from compare_core import RunError, compare, compare_refused
from oracle_pubkey import signature_spends
from oracle_script import harness_refused, locktime_sets

PIN = 'e0a1c157791544e818c901bd9341896965afbf9d'
CLASSES = ('verdict', 'digest', 'crash', 'timeout', 'unsupported', 'refusal')
INPUTS = ('signed-spends', 'cltv', 'csv', 'signed-digests')
FORMAT = 'dogelib-campaign-failure/1'


def canonical(value):
    """Encode canonical request text for the saved file's SHA-256 name."""
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True)


def selected_cases(names, seed):
    """Shuffle existing requests with the run seed, without constructing mutations."""
    timelocks = locktime_sets()
    groups = {'signed-spends': signature_spends(), 'cltv': timelocks[0][1], 'csv': timelocks[1][1]}
    records = [json.loads(line) for line in (ROOT / 'tests/script/signed-spends/recovery.jsonl').read_text().splitlines()]
    groups['signed-digests'] = [dict(op='sighash.legacy', tx_hex=r['tx_hex'],
                                    input_index=r['input_index'], script_code_hex=r['redeem_script_hex'],
                                    hash_type=r['hash_type']) for r in records]
    cases = [(name, i, request) for name in names for i, request in enumerate(groups[name])]
    random.Random(seed).shuffle(cases)
    return [dict(input=name, source_index=i, request={**request, 'id': f'campaign-{j}'})
            for j, (name, i, request) in enumerate(cases)]


def run_captured(program, args, data, timeout, capture):
    """Capture bytes losslessly, including invalid UTF-8 and output before a timeout."""
    proc = subprocess.Popen([program, *args], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)
    timed_out = False
    try:
        out, err = proc.communicate(data.encode(), timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGKILL)
        out, err = proc.communicate()
    capture.update(stdout=out.decode('utf-8', errors='surrogateescape'),
                   stderr=err.decode('utf-8', errors='surrogateescape'), returncode=proc.returncode)
    try:
        out.decode('utf-8')
        err.decode('utf-8')
    except UnicodeDecodeError:
        raise RunError('MALFORMED', f'{program}: non-UTF-8 process output', capture)
    if timed_out:
        raise RunError('TIMEOUT', f'{program} did not finish within {timeout} seconds', capture)
    if proc.returncode:
        raise RunError('EXIT', f'{program} exited with status {proc.returncode}', capture)
    return capture['stdout']


def execute(program, requests, timeout, arguments=()):
    """Retain raw output and status, including responses before a stream failure."""
    capture = {}
    try:
        data = ''.join(canonical(request) + '\n' for request in requests)
        lines = run_captured(program, arguments, data, timeout, capture).splitlines()
        if len(lines) != len(requests):
            raise RunError('COUNT', f'{program}: {len(lines)} responses to {len(requests)} requests', capture)
        responses = []
        for request, line in zip(requests, lines):
            try:
                response = json.loads(line)
            except json.JSONDecodeError:
                raise RunError('MALFORMED', f'{program}: response is not JSON', capture)
            if not isinstance(response, dict):
                raise RunError('MALFORMED', f'{program}: response is not an object', capture)
            if response.get('id') != request['id']:
                raise RunError('ID', f'{program}: response identifier differs', capture)
            responses.append(response)
        return dict(responses=responses, timeout=timeout, **capture)
    except RunError as error:
        return dict(error=dict(code=error.code, message=str(error)), timeout=timeout, **error.capture)


def classify(request, ours, core):
    """Apply Q6 and distinguish excluded outcomes from compatibility disagreements."""
    try:
        if harness_refused(request):
            failure = compare_refused(request, ours, core)
            if failure is None:
                return 'refusal', 'core', 'Core assertion-domain guard', None
        else:
            failure = compare(request, ours, core)
            if failure is None:
                if ours.get('ok', {}).get('result') == 'unsupported':
                    # compare validates both Script result shapes before this exemption.
                    return 'unsupported', 'lean', ours['ok']['reason'], None
                return None
        return ('digest' if request['op'] == 'sighash.legacy' else 'verdict',
                'undetermined', failure[1], failure[0])
    except (KeyError, TypeError, ValueError, AttributeError) as error:
        return 'crash', 'undetermined', f'malformed response: {error}', 'MALFORMED'


def assess(requests, runs):
    """Classify stream errors before assessing the complete response pairs."""
    errors = [(side, run['error']) for side, run in runs.items() if 'error' in run]
    if errors:
        # An exit or malformed output takes priority over another side's timeout.
        kind = 'crash' if any(e['code'] != 'TIMEOUT' for _, e in errors) else 'timeout'
        side = errors[0][0] if len(errors) == 1 else 'both'
        return [(None, (kind, side, '; '.join(e['message'] for _, e in errors), errors[0][1]['code']))]
    return [(i, result) for i, request in enumerate(requests)
            if (result := classify(request, runs['lean']['responses'][i], runs['core']['responses'][i]))]


def metadata(oracle, harness, timeout):
    """Record the tree, declared program versions and the adjacent harness build stamp."""
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

    versions = {}
    for side, program in (('lean', oracle), ('core', harness)):
        capture = {}
        try:
            run_captured(program, ['--version'], '', timeout, capture)
        except RunError as error:
            capture = dict(error=error.code, **error.capture)
        versions[side] = capture
    stamp = pathlib.Path(harness).resolve().parent / 'core.stamp'
    return dict(dogelib=git('rev-parse', 'HEAD'), dirty=bool(git('status', '--porcelain')),
                core_pin=PIN, core_stamp=stamp.read_text() if stamp.exists() else None,
                versions=versions, CORE_SIGNER_BLOB=None)


def case_requests(case):
    """Keep stage-1 single requests and generated request groups in send order."""
    return case.get('requests', [case['request']] if 'request' in case else [])


def assess_cases(cases, runs):
    """Apply Q6 to requests, then the independently stated generated property."""
    requests = [r for case in cases for r in case_requests(case)]
    results = assess(requests, runs)
    if results and results[0][0] is None:
        return results
    grouped, offset = [], 0
    for index, case in enumerate(cases):
        size = len(case_requests(case))
        local = {side: dict(run, responses=run['responses'][offset:offset + size]) for side, run in runs.items()}
        q6 = [result for i, result in results if offset <= i < offset + size]
        prop = None
        if 'expected' in case:
            from campaign_generator import property_result
            prop = property_result(case, local)
        if prop or q6:
            grouped.append((index, prop or q6[0]))
        offset += size
    return grouped


def prepare_generated(args, plans, timeout):
    """Sign a batch and check every signing digest before constructing spends."""
    from campaign_generator import signing_requests, materialize
    signing = [signing_requests(case['plan'], f"generated-{case['case_index']}") for case in plans]
    flat = [r for group in signing for r in group]
    signed = execute(args.signer, flat, timeout, ['--sign'])
    if 'error' in signed:
        entries = [dict(request=r, process=signed) for r in flat]
    else:
        entries = [dict(request=r, response=s) for r, s in zip(flat, signed['responses'])]
    checks = [dict({k: v for k, v in r.items() if k != 'key_ids'}, op='sighash.legacy') for r in flat]
    # A structured signer refusal has no digest and never reaches either oracle.
    if 'error' in signed or any('error' in e['response'] for e in entries):
        return None, entries, signed
    runs = {side: execute(program, checks, timeout) for side, program in (('lean', args.oracle), ('core', args.harness))}
    if assess(checks, runs):
        return None, entries, dict(preflight_requests=checks, oracle_runs=runs)
    if any(run['responses'][i].get('ok', {}).get('digest_hex') != e['response']['ok']['digest_hex']
           for run in runs.values() for i, e in enumerate(entries)):
        return None, entries, dict(preflight_requests=checks, oracle_runs=runs, signer_digest=True)
    offset, cases = 0, []
    for case, requests in zip(plans, signing):
        size = len(requests)
        built = materialize(case['plan'], f"generated-{case['case_index']}", entries[offset:offset + size])
        built['case_index'] = case['case_index']
        cases.append(built)
        offset += size
    return cases, entries, runs


def run_campaign(args, cases=None):
    """Run bounded batches, isolate stream failures and save complete evidence locally."""
    started = time.monotonic()
    deadline = started + args.seconds
    generated = args.campaign == 'generated'
    if cases is None and generated:
        from campaign_generator import plans
        seeds = selected_cases(['signed-spends'], args.seed)
        cases = seeds + [dict(plan=p) for p in plans(args.seed, max(0, args.cases - len(seeds)))]
    cases = selected_cases(args.inputs, args.seed) if cases is None else cases
    cases = cases[:args.cases]
    # Probe the programs first, so that an invocation error leaves no empty run directory.
    revisions = metadata(args.oracle, args.harness, 0.25)
    output = pathlib.Path(args.output) / f'run-{args.seed}-{time.time_ns()}'
    output.mkdir(parents=True, exist_ok=False)
    (output / 'failures').mkdir()
    build = dict(lean_toolchain=(ROOT / 'lean-toolchain').read_text().strip(),
                 python=sys.version, machine=platform.uname()._asdict())
    counts = dict.fromkeys(CLASSES, 0)
    counts.update(pass_count=0, known=0)
    batch_counts = dict(crash=0, timeout=0)
    saved, completed, attempts = [], 0, 0
    coverage = {key: {} for key in ('branches', 'hash_types', 'errors', 'mutations', 'properties', 'modes',
                                   'input_positions', 'input_counts', 'output_counts', 'selectors', 'flags')}

    def reach(key, value):
        name = str(value)
        coverage[key][name] = coverage[key].get(name, 0) + 1

    def save(batch, result, runs, history):
        kind, side, message, code = result
        requests = [r for case in batch for r in case_requests(case)]
        signer = [entry for case in batch for entry in case.get('signer', [])]
        text = canonical(requests[0]) if len(requests) == 1 else canonical(requests or signer)
        digest = hashlib.sha256(text.encode()).hexdigest()
        path = output / 'failures' / f'{digest}.json'
        replay = shlex.join([sys.executable, '-I', str(ROOT / 'scripts/campaign.py'), 'replay',
                             str(path.resolve()), args.oracle, args.harness])
        if side == 'signer':
            replay += ' --signer ' + shlex.quote(args.signer)
        record = dict(format=FORMAT, campaign=args.campaign, seed=args.seed,
                      case_index=batch[0]['case_index'], budget=dict(cases=args.cases, seconds=args.seconds),
                      property=batch[0].get('expected', {}).get('property', 'Q6'), **{'class': kind}, failing_side=side,
                      plan=dict(mode='generated' if generated else 'existing', inputs=[{k: v for k, v in case.items()
                                                                                       if k not in ('request', 'requests', 'signer')} for case in batch]),
                      requests=requests, signer=signer, responses=runs,
                      expected=batch[0].get('expected', dict(relation='compare_core.compare agreement',
                                    text='Design record 0009, section 11, Q6. No independent verdict is asserted.'),
                      ),
                      revisions=revisions, build=build, replay=replay, reduced_from=None,
                      detail=dict(message=message, code=code), timeout=args.timeout,
                      batch_failures=history)
        path.write_text(json.dumps(record, indent=2) + '\n')
        saved.append(str(path))

    def visit(batch, history):
        nonlocal completed, attempts
        if time.monotonic() >= deadline:
            return False
        pending = [case for case in batch if 'plan' in case and 'requests' not in case]
        if generated and pending:
            if len(pending) != len(batch):
                return visit([case for case in batch if case not in pending], history) and visit(pending, history)
            built, entries, evidence = prepare_generated(args, batch, min(args.timeout, max(0.001, deadline - time.monotonic())))
            if time.monotonic() >= deadline:
                return False
            if built is None:
                if len(batch) > 1:
                    middle = len(batch) // 2
                    return visit(batch[:middle], history) and visit(batch[middle:], history)
                batch[0]['signer'] = entries
                result = ('digest', 'signer', 'signing digest preflight failed', 'SIGNER_DIGEST')
                if 'oracle_runs' in evidence:
                    batch[0]['requests'] = evidence['preflight_requests']
                    if not evidence.get('signer_digest'):
                        result = assess(batch[0]['requests'], evidence['oracle_runs'])[0][1]
                    evidence = evidence['oracle_runs']
                elif 'error' in evidence:
                    result = ('timeout' if evidence['error']['code'] == 'TIMEOUT' else 'crash', 'signer',
                              'signer process failed', evidence['error']['code'])
                elif any('error' in e.get('response', {}) for e in entries):
                    result = ('refusal', 'signer', 'signer refused request', 'SIGNER_REFUSAL')
                counts[result[0]] += 1
                completed += 1
                save(batch, result, evidence, history)
                return True
            batch = built
            for entry in entries:
                revisions['CORE_SIGNER_BLOB'] = entry['response']['ok']['CORE_SIGNER_BLOB']
                revisions['signer_request_blob'] = entry['response']['ok']['request_source_blob']
        requests = [r for case in batch for r in case_requests(case)]
        runs = {}
        for side, program in (('lean', args.oracle), ('core', args.harness)):
            # Do not impose an artificial timeout after the campaign budget expires.
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                if any('error' in run for run in runs.values()):
                    runs[side] = dict(not_run='campaign time budget expired')
                    break
                return False
            runs[side] = execute(program, requests, min(args.timeout, remaining))
            if remaining < args.timeout and runs[side].get('error', {}).get('code') == 'TIMEOUT':
                # The campaign deadline does not establish a program timeout.
                if any('error' in run for name, run in runs.items() if name != side):
                    runs[side] = dict(not_run='campaign time budget expired')
                    break
                return False
        attempts += 1
        results = assess_cases(batch, runs)
        if results and results[0][0] is None and len(batch) > 1:
            evidence = history + [dict(requests=requests, responses=runs)]
            middle = len(batch) // 2
            before = counts['crash'] + counts['timeout'] + sum(batch_counts.values())
            left = visit(batch[:middle], evidence)
            right = visit(batch[middle:], evidence)
            attributed = counts['crash'] + counts['timeout'] + sum(batch_counts.values()) != before
            if left and right and not attributed:
                # A batch-only failure must retain the original stream for replay.
                batch_counts[results[0][1][0]] += 1
                save(batch, results[0][1], runs, history)
            elif not (left and right) and not attributed:
                save(batch, results[0][1], runs, history)
                batch_counts[results[0][1][0]] += 1
            return left and right
        completed += len(batch)
        counts['pass_count'] += len(batch) - len(results)
        failed = {index for index, _ in results}
        offset = 0
        for index, case in enumerate(batch):
            size = len(case_requests(case))
            if 'expected' in case:
                p = case['plan']
                for key, value in (('branches', p['branch']), ('modes', p['mode']),
                                   ('properties', case['expected']['property']), ('input_positions', p['n']),
                                   ('input_counts', len(p['tx']['inputs'])), ('output_counts', len(p['tx']['outputs'])),
                                   ('selectors', p['selector']), ('flags', p['flags'])):
                    reach(key, value)
                for h in p['hash_types']:
                    reach('hash_types', h)
                for m in p['mutations']:
                    reach('mutations', m['field'])
                reach('mutations', p['signature_mutation'])
                if 'error' not in runs['core']:
                    reach('errors', runs['core']['responses'][offset + size - 1].get('ok', {}).get('script_error', 'OK'))
                if index not in failed and case['expected'].get('known'):
                    counts['pass_count'] -= 1
                    counts['known'] += 1
            offset += size
        for index, result in results:
            counts[result[0]] += 1
            selected = batch if index is None else [batch[index]]
            if index is None:
                evidence = runs
            else:
                start = sum(len(case_requests(c)) for c in batch[:index])
                end = start + len(case_requests(batch[index]))
                evidence = {side: dict(run, responses=run['responses'][start:end], stdout_requests=requests)
                            for side, run in runs.items()}
            save(selected, result, evidence, history)
        return True

    for index, case in enumerate(cases):
        case['case_index'] = index
    for offset in range(0, len(cases), args.batch_size):
        if not visit(cases[offset:offset + args.batch_size], []):
            break
    failures = sum(counts[k] for k in ('verdict', 'digest', 'crash', 'timeout')) + sum(batch_counts.values())
    summary = dict(output=str(output), campaign=args.campaign, seed=args.seed, budget=dict(cases=args.cases, seconds=args.seconds),
                   inputs=args.inputs, selection=[{k: v for k, v in case.items() if k != 'request'} for case in cases], coverage=coverage,
                   selected=len(cases), completed=completed,
                   exhausted=completed < len(cases), counts=counts, batch_counts=batch_counts, failures=failures,
                   saved=saved, revisions=revisions, batch_size=args.batch_size,
                   timeout=args.timeout, batches_executed=attempts, elapsed_seconds=time.monotonic() - started)
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    return summary


def replay(args):
    """Resend saved requests unchanged and compare their class and failing side."""
    record = json.loads(pathlib.Path(args.failure).read_text())
    if record['format'] != FORMAT:
        raise ValueError('unsupported saved-failure format')
    if record['signer'] and record['failing_side'] == 'signer':
        if not getattr(args, 'signer', None):
            raise ValueError('signer failures require replay --signer PATH')
        entries = record['signer']
        rerun = execute(args.signer, [e['request'] for e in entries], record['timeout'], ['--sign'])
        if 'process' in entries[0]:
            stored = entries[0]['process']
            reproduced = (rerun.get('error', {}).get('code') == stored.get('error', {}).get('code') and
                          rerun.get('returncode') == stored.get('returncode') and
                          rerun.get('stdout') == stored.get('stdout') and rerun.get('stderr') == stored.get('stderr'))
        else:
            reproduced = rerun.get('responses') == [e['response'] for e in entries]
            if record['class'] == 'digest' and reproduced:
                checks = [dict({k: v for k, v in e['request'].items() if k != 'key_ids'}, op='sighash.legacy') for e in entries]
                probes = [execute(p, checks, record['timeout']) for p in (args.oracle, args.harness)]
                reproduced = any('error' not in run and
                                 any(s.get('ok', {}).get('digest_hex') != e['response']['ok']['digest_hex']
                                     for s, e in zip(run['responses'], entries)) for run in probes)
        print(json.dumps(dict(reproduced=reproduced, **{'class': record['class']}, failing_side='signer')))
        return 0 if reproduced else 1
    requests = record['requests']
    runs = {side: execute(program, requests, record['timeout'])
            for side, program in (('lean', args.oracle), ('core', args.harness))}
    if record.get('plan', {}).get('mode') == 'generated' and record.get('property') != 'Q6':
        cases, offset, signer_offset = [], 0, 0
        for item in record['plan']['inputs']:
            size = 2 * len(item['plan']['key_ids']) + 1
            nsign = len(item['plan']['key_ids'])
            cases.append(dict(item, requests=requests[offset:offset + size],
                              signer=record['signer'][signer_offset:signer_offset + nsign]))
            offset += size
            signer_offset += nsign
        results = assess_cases(cases, runs)
    else:
        results = assess(requests, runs)
    reproduced = any(result[0] == record['class'] and result[1] == record['failing_side']
                     for _, result in results)
    print(json.dumps(dict(reproduced=reproduced, **{'class': record['class']},
                          failing_side=record['failing_side'])))
    return 0 if reproduced else 1


def positive(text):
    """Accept a finite positive duration."""
    value = float(text)
    if not math.isfinite(value) or value <= 0:
        raise argparse.ArgumentTypeError('must be finite and positive')
    return value


def positive_int(text):
    """Accept a positive count."""
    value = int(text)
    if value <= 0:
        raise argparse.ArgumentTypeError('must be positive')
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    run = commands.add_parser('run')
    run.add_argument('--campaign', default='existing')
    run.add_argument('--signer', help='core-signer executable, required for --campaign generated')
    run.add_argument('--seed', type=int, required=True)
    run.add_argument('--cases', type=positive_int, default=10000)
    run.add_argument('--seconds', type=positive, default=600)
    run.add_argument('--timeout', type=positive, default=60)
    run.add_argument('--batch-size', type=positive_int, default=2000)
    run.add_argument('--inputs', nargs='+', choices=INPUTS, default=list(INPUTS[:3]))
    run.add_argument('--output', required=True, help='parent directory for fresh runs under build/campaign/')
    again = commands.add_parser('replay')
    again.add_argument('--signer', help='replay signing requests for a signer failure')
    again.add_argument('failure')
    for command in (run, again):
        command.add_argument('oracle')
        command.add_argument('harness')
    args = parser.parse_args()
    args.oracle = str(pathlib.Path(args.oracle).resolve())
    args.harness = str(pathlib.Path(args.harness).resolve())
    if args.signer:
        args.signer = str(pathlib.Path(args.signer).resolve())
    try:
        if args.command == 'run' and args.campaign == 'generated' and not args.signer:
            parser.error('--campaign generated requires --signer')
        for program in (args.oracle, args.harness, *([args.signer] if args.signer else [])):
            if not pathlib.Path(program).is_file() or not os.access(program, os.X_OK):
                raise OSError(f'program is absent or not executable: {program}')
        if args.command == 'replay':
            return replay(args)
        output = pathlib.Path(args.output).resolve()
        if not output.is_relative_to(ROOT / 'build/campaign'):
            parser.error('--output must be under this worktree\'s build/campaign/')
        summary = run_campaign(args)
        # Public logs contain counts, never candidate requests or responses.
        print(json.dumps({k: summary[k] for k in ('output', 'completed', 'counts', 'batch_counts', 'failures', 'exhausted')}))
        return 1 if summary['failures'] or summary['exhausted'] else 0
    except (OSError, ValueError, KeyError) as error:
        print(f'campaign: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
