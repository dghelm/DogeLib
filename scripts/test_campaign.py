"""Check campaign capture, bisection and replay with process wrappers.

Usage: python3 -I scripts/test_campaign.py <dogelib-oracle> <core-oracle>
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


def wrap(mode, program, args):
    """Mutate one exact request's response, or fail after flushing its predecessors."""
    if args:
        return subprocess.call([program, *args])
    requests = [json.loads(line) for line in sys.stdin]
    run = subprocess.run([program], input=''.join(json.dumps(r) + '\n' for r in requests),
                         capture_output=True, text=True, check=True)
    responses = [json.loads(line) for line in run.stdout.splitlines()]
    for request, response in zip(requests, responses):
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
    args = parser.parse_args()
    args.oracle = str(pathlib.Path(args.oracle).resolve())
    args.harness = str(pathlib.Path(args.harness).resolve())
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
        for mode in (*campaign.CLASSES, 'malformed', 'id', 'count'):
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
            expected = 'crash' if mode in ('malformed', 'id', 'count') else mode
            assert summary['completed'] == 8, summary
            assert summary['counts'][expected] == 1, summary
            assert summary['counts']['pass_count'] == 7, summary
            assert len(summary['saved']) == 1, summary
            record_path = pathlib.Path(summary['saved'][0])
            record = json.loads(record_path.read_text())
            assert record['case_index'] == 3
            assert record['requests'] == [chosen[3]['request']]
            assert record_path.stem == hashlib.sha256(campaign.canonical(record['requests'][0]).encode()).hexdigest()
            assert record['signer'] == []
            if mode in ('crash', 'timeout'):
                assert record['batch_failures']
                parent = record['batch_failures'][0]['responses']['core']
                assert len(parent['stdout'].splitlines()) == 3
                assert 'planted ' + mode in parent['stderr']
                if mode == 'crash':
                    assert len(parent['stderr']) > 2000
                    assert record['responses']['core']['returncode'] == 3
            replay = subprocess.run([sys.executable, '-I', str(ROOT / 'scripts/campaign.py'), 'replay',
                                     str(record_path), local.oracle, local.harness], capture_output=True, text=True)
            assert replay.returncode == 0, replay.stderr + replay.stdout
            assert json.loads(replay.stdout)['reproduced'] is True
            if mode not in ('unsupported', 'refusal'):
                clean = subprocess.run([sys.executable, '-I', str(ROOT / 'scripts/campaign.py'), 'replay',
                                        str(record_path), args.oracle, args.harness], capture_output=True, text=True)
                assert clean.returncode == 1, clean.stderr + clean.stdout
                assert json.loads(clean.stdout)['reproduced'] is False
            print(f'ok {mode}: saved case 3, replay {expected}')
            checks += 1
        batch = copy.deepcopy(options)
        batch.output = str(tmp / 'batch-only')
        batch.harness = wrapper(tmp / 'batch-only-core', 'batch-only', args.harness)
        summary = campaign.run_campaign(batch, copy.deepcopy(cases))
        assert summary['counts']['crash'] == 1 and len(summary['saved']) == 1
        record = json.loads(pathlib.Path(summary['saved'][0]).read_text())
        assert len(record['requests']) == 2
        assert record['case_index'] == 2
        reproduced = subprocess.run([sys.executable, '-I', str(ROOT / 'scripts/campaign.py'), 'replay',
                                     summary['saved'][0], batch.oracle, batch.harness],
                                    capture_output=True, text=True)
        assert reproduced.returncode == 0, reproduced.stderr + reproduced.stdout
        print('ok batch-only: retain and replay the failing pair after single requests pass')
        checks += 1
        exhausted = copy.deepcopy(options)
        exhausted.output = str(tmp / 'exhausted')
        exhausted.seconds = 0.000001
        summary = campaign.run_campaign(exhausted, copy.deepcopy(cases))
        assert summary['exhausted'] and summary['completed'] == 0
        print('ok budget: incomplete run cannot count as a clean campaign')
        checks += 1
        limited = copy.deepcopy(options)
        limited.output = str(tmp / 'limited-timeout')
        limited.timeout, limited.seconds = 5, 0.5
        limited.harness = wrapper(tmp / 'limited-core', 'timeout', args.harness)
        summary = campaign.run_campaign(limited, [copy.deepcopy(cases[3])])
        assert summary['counts']['timeout'] == 1 and len(summary['saved']) == 1
        record = json.loads(pathlib.Path(summary['saved'][0]).read_text())
        assert record['responses']['core']['timeout'] < limited.timeout
        reproduced = subprocess.run([sys.executable, '-I', str(ROOT / 'scripts/campaign.py'), 'replay',
                                     summary['saved'][0], limited.oracle, limited.harness],
                                    capture_output=True, text=True)
        assert reproduced.returncode == 0, reproduced.stderr + reproduced.stdout
        print('ok time limit: replay retains the effective invocation timeout')
        checks += 1
        options.output = str(tmp / 'clean')
        summary = campaign.run_campaign(options, cases)
        assert summary['failures'] == 0 and not summary['saved'] and summary['counts']['pass_count'] == 8
        assert all(summary['counts'][kind] == 0 for kind in campaign.CLASSES)
        assert summary['revisions']['core_stamp']
        assert summary['inputs'] == ['cltv'] and summary['seed'] == options.seed
        assert campaign.selected_cases(['cltv'], 1) == campaign.selected_cases(['cltv'], 1)
        assert campaign.selected_cases(['cltv'], 1) != campaign.selected_cases(['cltv'], 2)
        print('ok clean: eight passes, zero in all six outcome classes')
        checks += 1
    print(f'{checks} cases, 0 failures')
    return 0


if __name__ == '__main__':
    sys.exit(main())
