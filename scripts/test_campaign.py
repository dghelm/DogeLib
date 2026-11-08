"""Check campaign capture, bisection and replay with process wrappers.

Usage: python3 -I scripts/test_campaign.py <dogelib-oracle> <core-oracle> [--signer PATH] [--proposal-replay PATH]
"""

import argparse
import copy
import hashlib
import json
import pathlib
import shlex
import subprocess
import sys
import tempfile
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
import campaign
from oracle_script import refused_set


def check(condition, detail='campaign self-test check failed'):
    """Keep self-test checks active when Python optimizes bytecode."""
    if not condition:
        raise RuntimeError(detail)


def wrap(mode, program, args):
    """Mutate one exact request's response, or fail after flushing its predecessors."""
    if mode == 'error-all':
        # A stand-in that ignores its arguments and answers every request with an error object.
        for line in sys.stdin:
            request = json.loads(line)
            print(json.dumps(dict(id=request['id'], error=dict(kind='request', message='stand-in'))), flush=True)
        return 0
    if mode == 'signer-shape' and args == ['--sign']:
        for line in sys.stdin:
            request = json.loads(line)
            print(json.dumps(dict(id=request['id'], ok=dict(digest_hex='broken'))), flush=True)
        return 0
    if args:
        if mode == 'version-hang':
            time.sleep(30)
        return subprocess.call([program, *args])
    requests = [json.loads(line) for line in sys.stdin]
    run = subprocess.run([program], input=''.join(json.dumps(r) + '\n' for r in requests),
                         capture_output=True, text=True, check=True)
    responses = [json.loads(line) for line in run.stdout.splitlines()]
    for request, response in zip(requests, responses):
        if mode.startswith('M'):
            from test_campaign_generator import m3_trigger, mutate_response
            height_response = None
            if mode == 'M3' and m3_trigger(request, response):
                probe = dict(request, flags=request['flags'] & ~512)
                height = subprocess.run([program], input=json.dumps(probe) + '\n',
                                        capture_output=True, text=True, check=True)
                height_response = json.loads(height.stdout)
            action = mutate_response(mode, request, response, height_response)
            if action == 'crash':
                return 3
            if action == 'timeout':
                time.sleep(30)
        if mode == 'q6-after' and '-after-' in request['id']:
            response['ok']['digest_hex'] = '00' * 32
        if request['id'] == 'campaign-3':
            if mode == 'batch-only' and len(requests) > 1:
                return 3
            if mode == 'crash':
                sys.stderr.write('planted crash\n' + 'x' * 2000)
                return 3
            if mode == 'timeout':
                print('planted timeout', file=sys.stderr, flush=True)
                time.sleep(30)
            if mode == 'malformed':
                print('{', flush=True)
                continue
            if mode in ('nonutf8-stdout', 'nonutf8-stderr'):
                stream = sys.stdout if mode == 'nonutf8-stdout' else sys.stderr
                stream.buffer.write(b'\xff\n')
                stream.flush()
            if mode == 'id':
                response['id'] = 'wrong'
            if mode == 'count':
                continue
            if mode == 'verdict':
                response['ok'] = dict(result='rejected', script_error='EVAL_FALSE')
            if mode == 'digest':
                response['ok']['digest_hex'] = '00' * 32
        print(json.dumps(response), flush=True)
    return 0


def wrapper(path, mode, program):
    """Write a wrapper within the worktree's uncommitted build directory."""
    command = [sys.executable, '-I', str(pathlib.Path(__file__).resolve()), '--wrap', mode, program]
    path.write_text('#!/bin/sh\nexec ' + shlex.join(command) + ' "$@"\n')
    path.chmod(0o755)
    return str(path)


def main():
    if len(sys.argv) >= 4 and sys.argv[1] == '--wrap':
        return wrap(sys.argv[2], sys.argv[3], sys.argv[4:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('oracle')
    parser.add_argument('harness')
    parser.add_argument('--signer', help='defaults to core-signer beside the harness')
    parser.add_argument('--proposal-replay', help='defaults to proposal-replay beside the oracle')
    args = parser.parse_args()
    args.oracle = str(pathlib.Path(args.oracle).resolve())
    args.harness = str(pathlib.Path(args.harness).resolve())
    args.proposal_replay = args.proposal_replay or str(pathlib.Path(args.oracle).with_name('proposal-replay'))
    base = ROOT / 'build/campaign'
    base.mkdir(parents=True, exist_ok=True)
    checks = 0
    with tempfile.TemporaryDirectory(prefix='selftest-', dir=base) as tmp:
        tmp = pathlib.Path(tmp)
        options = argparse.Namespace(campaign='selftest', seed=20261108, cases=8, seconds=60,
                                     timeout=1, batch_size=8, inputs=['cltv'],
                                     oracle=args.oracle, harness=args.harness)
        cases = campaign.selected_cases(['cltv'], options.seed)[:8]
        # Use accepted boundary requests so a rejection mutant always changes the verdict.
        from oracle_script import locktime_sets
        accepted = locktime_sets()[0][1][1]  # operand zero, lock time zero, nonfinal sequence
        for case in cases:
            case['request'] = dict(accepted, id=case['request']['id'])
        for mode in (*campaign.CLASSES, 'malformed', 'id', 'count', 'nonutf8-stdout', 'nonutf8-stderr'):
            local = copy.deepcopy(options)
            local.output = str(tmp / mode)
            chosen = copy.deepcopy(cases)
            if mode == 'digest':
                digest = campaign.selected_cases(['signed-digests'], options.seed)[0]['request']
                for case in chosen:
                    case['request'] = dict(digest, id=case['request']['id'])
            if mode in ('unsupported', 'refusal'):
                chosen[3]['request'] = dict(chosen[3]['request'], flags=64) if mode == 'unsupported' else dict(refused_set()[0], id='campaign-3')
                # These wrappers preserve real excluded responses, rather than inventing malformed ones.
                local.oracle = wrapper(tmp / f'{mode}-lean', mode, args.oracle)
            else:
                local.harness = wrapper(tmp / f'{mode}-core', mode, args.harness)
            summary = campaign.run_campaign(local, chosen)
            expected = 'crash' if mode in ('malformed', 'id', 'count', 'nonutf8-stdout', 'nonutf8-stderr') else mode
            check(summary['completed'] == 8, summary)
            check(summary['counts'][expected] == 1, summary)
            check(summary['counts']['pass_count'] == 7, summary)
            check(len(summary['saved']) == 1, summary)
            record_path = pathlib.Path(summary['saved'][0])
            record = json.loads(record_path.read_text())
            check(record['case_index'] == 3, 'check failed at line 119')
            check(record['requests'] == [chosen[3]['request']], 'check failed at line 120')
            check(record_path.stem == hashlib.sha256(campaign.canonical(record['requests'][0]).encode()).hexdigest(), 'check failed at line 121')
            check(record['signer'] == [], 'check failed at line 122')
            if mode == 'verdict':
                evidence = record['responses']['core']
                printed = json.dumps(evidence['responses'][0]) + '\n'
                if printed not in evidence['stdout'] or evidence['stdout_requests'] != [c['request'] for c in chosen]:
                    raise RuntimeError('per-request record lost the original response stream')
            if mode.startswith('nonutf8-'):
                stream = mode.removeprefix('nonutf8-')
                if b'\xff' not in record['responses']['core'][stream].encode('utf-8', errors='surrogateescape'):
                    raise RuntimeError('invalid output bytes were lost')
            if mode in ('crash', 'timeout'):
                check(record['batch_failures'], 'check failed at line 133')
                parent = record['batch_failures'][0]['responses']['core']
                check(len(parent['stdout'].splitlines()) == 3, 'check failed at line 135')
                check('planted ' + mode in parent['stderr'], 'check failed at line 136')
                if mode == 'crash':
                    check(len(parent['stderr']) > 2000, 'check failed at line 138')
                    check(record['responses']['core']['returncode'] == 3, 'check failed at line 139')
            replay = subprocess.run([sys.executable, '-I', str(ROOT / 'scripts/campaign.py'), 'replay',
                                     str(record_path), local.oracle, local.harness], capture_output=True, text=True)
            check(replay.returncode == 0, replay.stderr + replay.stdout)
            check(json.loads(replay.stdout)['reproduced'] is True, 'check failed at line 143')
            if mode == 'crash':
                blocked = tmp / 'non-executable'
                blocked.write_text('not executable\n')
                invalid_executable = tmp / 'invalid-executable'
                invalid_executable.write_text('#!/missing/campaign-interpreter\n')
                invalid_executable.chmod(0o755)
                for bad in (tmp / 'missing', blocked, invalid_executable):
                    for side in (0, 1):
                        programs = [local.oracle, local.harness]
                        programs[side] = str(bad)
                        for command in (['replay', str(record_path)],
                                        ['run', '--seed', '1', '--output', str(tmp / 'invalid')]):
                            invalid = subprocess.run([sys.executable, '-I', str(ROOT / 'scripts/campaign.py'),
                                                      *command, *programs], capture_output=True, text=True)
                            if invalid.returncode != 2 or invalid.stdout:
                                raise RuntimeError(f'invocation error became evidence: {invalid}')
                print('ok invocation: run and replay reject missing and non-executable programs on both sides')
            if mode not in ('unsupported', 'refusal'):
                clean = subprocess.run([sys.executable, '-I', str(ROOT / 'scripts/campaign.py'), 'replay',
                                        str(record_path), args.oracle, args.harness], capture_output=True, text=True)
                check(clean.returncode == 1, clean.stderr + clean.stdout)
                check(json.loads(clean.stdout)['reproduced'] is False, 'check failed at line 162')
            print(f'ok {mode}: saved case 3, replay {expected}')
            checks += 1
        batch = copy.deepcopy(options)
        batch.output = str(tmp / 'batch-only')
        batch.harness = wrapper(tmp / 'batch-only-core', 'batch-only', args.harness)
        summary = campaign.run_campaign(batch, copy.deepcopy(cases))
        check(summary['batch_counts']['crash'] == 1 and len(summary['saved']) == 1, 'check failed at line 169')
        if sum(summary['counts'].values()) != summary['completed'] or summary['failures'] != 1:
            raise RuntimeError(f'batch evidence inflated per-case counts: {summary}')
        record = json.loads(pathlib.Path(summary['saved'][0]).read_text())
        check(len(record['requests']) == 2, 'check failed at line 173')
        check(record['case_index'] == 2, 'check failed at line 174')
        reproduced = subprocess.run([sys.executable, '-I', str(ROOT / 'scripts/campaign.py'), 'replay',
                                     summary['saved'][0], batch.oracle, batch.harness],
                                    capture_output=True, text=True)
        check(reproduced.returncode == 0, reproduced.stderr + reproduced.stdout)
        print('ok batch-only: retain and replay the failing pair after single requests pass')
        checks += 1
        from unittest.mock import patch
        interrupted = copy.deepcopy(options)
        interrupted.output = str(tmp / 'interrupted-isolation')
        clock = [0]
        original_execute = campaign.execute

        def expire_after_crash(program, requests, timeout):
            result = original_execute(program, requests, timeout)
            if len(requests) == 1 and requests[0]['id'] == 'campaign-3' and 'error' in result:
                clock[0] = 100
            return result

        interrupted.harness = wrapper(tmp / 'interrupted-core', 'crash', args.harness)
        with patch.object(campaign.time, 'monotonic', side_effect=lambda: clock[0]), \
                patch.object(campaign, 'execute', side_effect=expire_after_crash):
            summary = campaign.run_campaign(interrupted, copy.deepcopy(cases))
        if summary['counts']['crash'] != 1 or len(summary['saved']) != 1 or not summary['exhausted']:
            raise RuntimeError(f'ancestors duplicated an attributed crash: {summary}')
        print('ok interrupted isolation: one crash remains one saved failure')
        checks += 1
        exhausted = copy.deepcopy(options)
        exhausted.output = str(tmp / 'exhausted')
        exhausted.seconds = 0.000001
        summary = campaign.run_campaign(exhausted, copy.deepcopy(cases))
        check(summary['exhausted'] and summary['completed'] == 0, 'check failed at line 205')
        print('ok budget: incomplete run cannot count as a clean campaign')
        checks += 1
        limited = copy.deepcopy(options)
        limited.output = str(tmp / 'limited-timeout')
        limited.timeout, limited.seconds = 5, 0.5
        limited.harness = wrapper(tmp / 'limited-core', 'timeout', args.harness)
        summary = campaign.run_campaign(limited, [copy.deepcopy(cases[3])])
        if not summary['exhausted'] or summary['completed'] != 0 or summary['saved'] or summary['counts']['timeout']:
            raise RuntimeError(f'budget exhaustion became a timeout: {summary}')
        # A saved timeout must replay with its configured limit, even for older records.
        from unittest.mock import patch
        record = dict(format=campaign.FORMAT, signer=[], requests=[cases[3]['request']],
                      timeout=10, responses={'lean': {'timeout': 0.01}, 'core': {'timeout': 0.01}},
                      failing_side='core', **{'class': 'timeout'})
        old = tmp / 'old-timeout.json'
        old.write_text(json.dumps(record))
        with patch.object(campaign, 'execute', return_value={'responses': []}) as execute, \
                patch.object(campaign, 'assess', return_value=[]):
            campaign.replay(argparse.Namespace(failure=str(old), oracle=args.oracle, harness=args.harness))
            if [call.args[2] for call in execute.call_args_list] != [10, 10]:
                raise RuntimeError('replay used a budget-shortened timeout')
        print('ok time limit: incomplete without evidence, replay uses configured timeout')
        checks += 1
        options.output = str(tmp / 'clean')
        probe = copy.deepcopy(options)
        probe.output = str(tmp / 'version-probe')
        probe.timeout = 10
        probe.harness = wrapper(tmp / 'version-core', 'version-hang', args.harness)
        started = time.monotonic()
        summary = campaign.run_campaign(probe, copy.deepcopy(cases))
        check(summary['revisions']['versions']['core']['error'] == 'TIMEOUT', summary)
        check(time.monotonic() - started < 3, 'version probe used the request timeout')
        check(summary['counts']['pass_count'] == 8, summary)
        print('ok version probe: hung version exits after a short fixed timeout')
        checks += 1
        summary = campaign.run_campaign(options, cases)
        check(summary['failures'] == 0 and not summary['saved'] and summary['counts']['pass_count'] == 8, 'check failed at line 231')
        check(all(summary['counts'][kind] == 0 for kind in campaign.CLASSES), 'check failed at line 232')
        check(summary['revisions']['core_stamp'], 'check failed at line 233')
        check(summary['inputs'] == ['cltv'] and summary['seed'] == options.seed, 'check failed at line 234')
        check(campaign.selected_cases(['cltv'], 1) == campaign.selected_cases(['cltv'], 1), 'check failed at line 235')
        check(campaign.selected_cases(['cltv'], 1) != campaign.selected_cases(['cltv'], 2), 'check failed at line 236')
        print('ok clean: eight passes, zero in all six outcome classes')
        checks += 1
    from test_campaign_generator import stage2
    checks += stage2(args, wrapper, check)
    from test_campaign_reducer import stage3
    checks += stage3(args, check, wrapper)
    print(f'{checks} cases, 0 failures')
    return 0


if __name__ == '__main__':
    sys.exit(main())
