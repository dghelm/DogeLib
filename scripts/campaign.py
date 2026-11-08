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


def execute(program, requests, timeout):
    """Retain raw output and status, including responses before a stream failure."""
    capture = {}
    try:
        data = ''.join(canonical(request) + '\n' for request in requests)
        lines = run_captured(program, [], data, timeout, capture).splitlines()
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
        except OSError as error:
            capture = dict(error=str(error))
        versions[side] = capture
    stamp = pathlib.Path(harness).resolve().parent / 'core.stamp'
    return dict(dogelib=git('rev-parse', 'HEAD'), dirty=bool(git('status', '--porcelain')),
                core_pin=PIN, core_stamp=stamp.read_text() if stamp.exists() else None,
                versions=versions, CORE_SIGNER_BLOB=None)


def run_campaign(args, cases=None):
    """Run bounded batches, isolate stream failures and save complete evidence locally."""
    started = time.monotonic()
    deadline = started + args.seconds
    cases = selected_cases(args.inputs, args.seed) if cases is None else cases
    cases = cases[:args.cases]
    output = pathlib.Path(args.output) / f'run-{args.seed}-{time.time_ns()}'
    output.mkdir(parents=True, exist_ok=False)
    (output / 'failures').mkdir()
    revisions = metadata(args.oracle, args.harness, min(args.timeout, args.seconds))
    build = dict(lean_toolchain=(ROOT / 'lean-toolchain').read_text().strip(),
                 python=sys.version, machine=platform.uname()._asdict())
    counts = dict.fromkeys(CLASSES, 0)
    counts.update(pass_count=0, known=0)
    saved, completed, attempts = [], 0, 0

    def save(batch, result, runs, history):
        kind, side, message, code = result
        requests = [case['request'] for case in batch]
        text = canonical(requests[0]) if len(requests) == 1 else canonical(requests)
        digest = hashlib.sha256(text.encode()).hexdigest()
        path = output / 'failures' / f'{digest}.json'
        replay = shlex.join([sys.executable, '-I', str(ROOT / 'scripts/campaign.py'), 'replay',
                             str(path.resolve()), args.oracle, args.harness])
        record = dict(format=FORMAT, campaign=args.campaign, seed=args.seed,
                      case_index=batch[0]['case_index'], budget=dict(cases=args.cases, seconds=args.seconds),
                      property='Q6', **{'class': kind}, failing_side=side,
                      plan=dict(mode='existing', inputs=[{k: v for k, v in case.items() if k != 'request'} for case in batch]),
                      requests=requests, signer=[], responses=runs,
                      expected=dict(relation='compare_core.compare agreement',
                                    text='Design record 0009, section 11, Q6. No independent verdict is asserted.'),
                      revisions=revisions, build=build, replay=replay, reduced_from=None,
                      detail=dict(message=message, code=code), timeout=args.timeout,
                      batch_failures=history)
        path.write_text(json.dumps(record, indent=2) + '\n')
        saved.append(str(path))

    def visit(batch, history):
        nonlocal completed, attempts
        if time.monotonic() >= deadline:
            return False
        requests = [case['request'] for case in batch]
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
        results = assess(requests, runs)
        if results and results[0][0] is None and len(batch) > 1:
            evidence = history + [dict(requests=requests, responses=runs)]
            middle = len(batch) // 2
            before = sum(counts[k] for k in ('crash', 'timeout'))
            left = visit(batch[:middle], evidence)
            right = visit(batch[middle:], evidence)
            if left and right and sum(counts[k] for k in ('crash', 'timeout')) == before:
                # A batch-only failure must retain the original stream for replay.
                counts[results[0][1][0]] += 1
                save(batch, results[0][1], runs, history)
            elif not (left and right) and sum(counts[k] for k in ('crash', 'timeout')) == before:
                save(batch, results[0][1], runs, history)
                counts[results[0][1][0]] += 1
            return left and right
        completed += len(batch)
        counts['pass_count'] += len(batch) - len(results)
        for index, result in results:
            counts[result[0]] += 1
            selected = batch if index is None else [batch[index]]
            if index is None:
                evidence = runs
            else:
                evidence = {side: dict(responses=[run['responses'][index]], returncode=run['returncode'], timeout=run['timeout'],
                                       stdout=canonical(run['responses'][index]) + '\n', stderr=run['stderr'])
                            for side, run in runs.items()}
            save(selected, result, evidence, history)
        return True

    for index, case in enumerate(cases):
        case['case_index'] = index
    for offset in range(0, len(cases), args.batch_size):
        if not visit(cases[offset:offset + args.batch_size], []):
            break
    failures = sum(counts[k] for k in ('verdict', 'digest', 'crash', 'timeout'))
    summary = dict(output=str(output), campaign=args.campaign, seed=args.seed, budget=dict(cases=args.cases, seconds=args.seconds),
                   inputs=args.inputs, selection=[{k: v for k, v in case.items() if k != 'request'} for case in cases],
                   selected=len(cases), completed=completed,
                   exhausted=completed < len(cases), counts=counts, failures=failures,
                   saved=saved, revisions=revisions, batch_size=args.batch_size,
                   timeout=args.timeout, batches_executed=attempts, elapsed_seconds=time.monotonic() - started)
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    return summary


def replay(args):
    """Resend saved requests unchanged and compare their class and failing side."""
    record = json.loads(pathlib.Path(args.failure).read_text())
    if record['format'] != FORMAT:
        raise ValueError('unsupported saved-failure format')
    if record['signer']:
        raise ValueError('signer replay belongs to stage 2')
    requests = record['requests']
    runs = {side: execute(program, requests, record['timeout'])
            for side, program in (('lean', args.oracle), ('core', args.harness))}
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
    run.add_argument('--seed', type=int, required=True)
    run.add_argument('--cases', type=positive_int, default=10000)
    run.add_argument('--seconds', type=positive, default=600)
    run.add_argument('--timeout', type=positive, default=60)
    run.add_argument('--batch-size', type=positive_int, default=2000)
    run.add_argument('--inputs', nargs='+', choices=INPUTS, default=list(INPUTS[:3]))
    run.add_argument('--output', required=True, help='parent directory for fresh runs under build/campaign/')
    again = commands.add_parser('replay')
    again.add_argument('failure')
    for command in (run, again):
        command.add_argument('oracle')
        command.add_argument('harness')
    args = parser.parse_args()
    args.oracle = str(pathlib.Path(args.oracle).resolve())
    args.harness = str(pathlib.Path(args.harness).resolve())
    try:
        for program in (args.oracle, args.harness):
            if not pathlib.Path(program).is_file() or not os.access(program, os.X_OK):
                raise OSError(f'program is absent or not executable: {program}')
        if args.command == 'replay':
            return replay(args)
        output = pathlib.Path(args.output).resolve()
        if not output.is_relative_to(ROOT / 'build/campaign'):
            parser.error('--output must be under this worktree\'s build/campaign/')
        summary = run_campaign(args)
        # Public logs contain counts, never candidate requests or responses.
        print(json.dumps({k: summary[k] for k in ('output', 'completed', 'counts', 'failures', 'exhausted')}))
        return 1 if summary['failures'] or summary['exhausted'] else 0
    except (OSError, ValueError, KeyError) as error:
        print(f'campaign: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
