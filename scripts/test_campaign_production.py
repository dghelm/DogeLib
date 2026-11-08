"""Stage 4 of design record 0009: production replay of a planted harness fault.

Usage: python3 -I scripts/test_campaign_production.py <dogelib-oracle> <core-oracle>
           [--signer PATH] [--node DIR] [--upstream-harness PATH]

The campaign searches with the planted harness fault M3 of section 8.2, reduces
the first detection, and replays it at L1 with the unchanged harness at the pin.
--node adds the L3 replay on regtest, which must classify the candidate as a
harness fault, and three ordinary L3 spends with known node verdicts.
--upstream-harness adds the L1 replay against a harness build of another
commit, and compares its responses with the pin harness on generated cases.
"""

import argparse
import copy
import json
import pathlib
import subprocess
import sys
import tempfile
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
import campaign
import campaign_production
from campaign_generator import expectation, mutated, plans
from campaign_reduce import condition, reduce_failure


def command(*arguments):
    """Run campaign.py and return its status and its single JSON line, if any."""
    run = subprocess.run([sys.executable, '-I', str(ROOT / 'scripts/campaign.py'), *arguments],
                         capture_output=True, text=True)
    output = json.loads(run.stdout) if run.stdout.strip() else None
    return run.returncode, output, run.stderr


def spend_plan(branch, lock_time=0, sequence=0xffffffff, signature_mutation='none'):
    """A one-input, one-output plan of the 2-of-3 template with standard flags."""
    plan = dict(mode='preserve', branch=branch, n=0, flags=543, signature_mutation=signature_mutation,
                mutations=[], key_ids=[1, 2] if branch == 'ordinary' else [4],
                hash_types=[1, 1] if branch == 'ordinary' else [1],
                selector='01' if branch == 'ordinary' else '',
                tx=dict(version=1, lock_time=lock_time,
                        inputs=[dict(outpoint='00' * 36, sequence=sequence, script_sig='')],
                        outputs=[dict(value=100000000, script='51')]))
    return plan, expectation(plan, mutated(plan))


def l3_positives(args, check, signer, node):
    """Three spends with known production verdicts, and the comparison that reports a reproduction."""
    programs = dict(lean=args.oracle, core=args.harness, signer=signer,
                    node=str(pathlib.Path(node) / 'core/src/dogecoind'))
    checks = 0
    ordinary, expected = spend_plan('ordinary')
    check(expected['property'] == 'Q1' and expected['verdict'] == 'accepted', expected)
    evidence = campaign_production.run_l3(ordinary, expected, programs, 60)
    check(evidence['mempool']['result'] == 'accepted' and evidence['block']['result'] == 'accepted', evidence['mempool'])
    check(evidence['outcome'] == 'not-reproduced' and not evidence['property_failures'], evidence['outcome'])
    print(f"ok L3 Q1: the node accepts an ordinary 2-of-3 spend in its mempool and in block "
          f"{evidence['chain']['height']} ({evidence['seconds']} s)")
    checks += 1
    # Lock time 1,000 is a height below the operand 1,000,000, and the chain is past it, so the spend is final.
    early, expected = spend_plan('recovery', lock_time=1000, sequence=0xfffffffe)
    check(expected['property'] == 'Q3' and expected['script_error'] == 'UNSATISFIED_LOCKTIME', expected)
    evidence = campaign_production.run_l3(early, expected, programs, 60)
    for side in ('mempool', 'block'):
        check(evidence[side]['result'] == 'rejected' and evidence[side]['script_error'] == 'UNSATISFIED_LOCKTIME',
              evidence[side])
    check(evidence['outcome'] == 'not-reproduced', evidence['outcome'])
    print(f"ok L3 Q3: the node rejects an early recovery spend in its mempool and in a block: "
          f"{evidence['block']['reason']} ({evidence['seconds']} s)")
    checks += 1
    # The comparison must report a reproduction when the node contradicts the saved expectation.
    contradicted = dict(expected, verdict='accepted')
    check(campaign_production.outcome(evidence['mempool'], contradicted, contradicted) == 'reproduced',
          'a node verdict against the expectation was not a reproduction')
    check(campaign_production.outcome(evidence['mempool'], contradicted, expected) == 'not-comparable',
          'a rebuilt case with another expectation was comparable')
    print('ok L3 comparison: a contradicting node verdict reproduces, and a changed case is not comparable')
    checks += 1
    high_s, expected = spend_plan('ordinary', signature_mutation='high_s')
    check(expected['script_error'] == 'SIG_HIGH_S', expected)
    evidence = campaign_production.run_l3(high_s, expected, programs, 60)
    check(evidence['mempool']['result'] == 'rejected' and evidence['mempool']['script_error'] == 'SIG_HIGH_S',
          evidence['mempool'])
    check(evidence['block']['result'] == 'accepted' and evidence['policy_only'], evidence['block'])
    check(evidence['outcome'] == 'not-reproduced', evidence['outcome'])
    print(f"ok L3 policy: LOW_S rejects a high-S spend in the mempool, and block flags "
          f"{campaign_production.BLOCK_FLAGS} accept it, so the replay reports policy_only "
          f"({evidence['seconds']} s)")
    checks += 1
    return checks


def upstream_sample(args, check, upstream, signer, count=500):
    """Send the requests of generated cases to both harness builds and count differing responses."""
    options = argparse.Namespace(signer=signer, oracle=args.oracle, harness=args.harness)
    batch = [dict(plan=p, case_index=i) for i, p in enumerate(plans(20261108, count))]
    built, _, _ = campaign.prepare_generated(options, batch, 60)
    check(built is not None, 'the generated sample failed its signing preflight')
    requests = [r for case in built for r in case['requests']]
    pin = campaign.execute(args.harness, requests, 120)
    other = campaign.execute(upstream, requests, 120)
    check('error' not in pin and 'error' not in other, 'a harness build failed on the generated sample')
    differing = [r['id'] for r, a, b in zip(requests, pin['responses'], other['responses']) if a != b]
    return len(requests), differing


def stage4(args, check, wrapper, node=None, upstream=None):
    """Find, reduce and replay the planted harness fault M3 of section 8.2."""
    signer = str(pathlib.Path(args.signer or pathlib.Path(args.harness).with_name('core-signer')).resolve())
    base = campaign.ROOT / 'build/campaign'
    base.mkdir(parents=True, exist_ok=True)
    checks = 0
    with tempfile.TemporaryDirectory(prefix='stage4-', dir=base) as tmp:
        tmp = pathlib.Path(tmp)
        planted = wrapper(tmp / 'M3-wrapper', 'M3', args.harness)
        options = argparse.Namespace(campaign='generated', signer=signer, seed=20261108, cases=3000,
                                     seconds=120, timeout=3, batch_size=16, inputs=['generated'],
                                     oracle=args.oracle, harness=planted, output=str(tmp / 'search'),
                                     stop_after_failure=True)
        started = time.monotonic()
        summary = campaign.run_campaign(options)
        found = [(json.loads(pathlib.Path(p).read_text()), p) for p in summary['saved']]
        found = [(r, p) for r, p in found if (r['class'], r['failing_side']) == ('verdict', 'core')]
        check(found, f"the planted fault M3 survived: {summary['counts']}")
        record, path = min(found, key=lambda item: item[0]['case_index'])
        target, reduced = reduce_failure(path, args.oracle, planted, signer)
        check(condition(reduced) == condition(record), 'the reduction changed the failure condition')
        searched = time.monotonic() - started
        status, output, error = command('replay', str(target), args.oracle, planted)
        check(status == 0 and output['reproduced'], f'the reduced failure does not replay: {error}')
        print(f"ok search: M3 found at case {record['case_index']} as {reduced['property']} "
              f"{reduced['class']} on the Core side, reduced with label {reduced['reduction']['label']}, "
              f"replay reproduced ({searched:.1f} s)")
        checks += 1

        before = target.read_text()
        for arguments, reason in (
                (['--level', 'L1', str(target), args.oracle, planted], 'a wrapper without a build stamp'),
                (['--level', 'L1', '--revision', '0' * 40, str(target), args.oracle, args.harness],
                 'a --revision that the build does not name'),
                (['--level', 'L3', str(target), args.oracle, args.harness], 'L3 without --node and --signer')):
            status, output, error = command('replay', *arguments)
            check(status == 2 and output is None, f'{reason} became evidence: {status} {output} {error}')
            check(target.read_text() == before, f'{reason} changed the saved failure')
        print('ok refusals: a wrapper, a wrong revision and an incomplete L3 call record nothing')
        checks += 1

        status, output, error = command('replay', '--level', 'L1', str(target), args.oracle, args.harness)
        check(status == 1 and output['outcome'] == 'not-reproduced', f'L1: {status} {output} {error}')
        check(output['revision'] == campaign.PIN and output['target'] == 'pin', output)
        check(output['classification'] == 'undetermined', 'L1 alone classified a verdict candidate')
        saved = json.loads(target.read_text())
        check(saved['format'] == campaign.FORMAT and len(saved['production']['replays']) == 1, saved.keys())
        check(saved['production']['replays'][0]['core_spend']['result'] == reduced['expected']['verdict'],
              'the unchanged harness does not give the expected verdict')
        print(f"ok L1 pin: the unchanged harness at {campaign.PIN[:7]} does not reproduce the candidate")
        checks += 1

        if upstream:
            started = time.monotonic()
            status, output, error = command('replay', '--level', 'L1', '--target', 'upstream',
                                            str(target), args.oracle, upstream)
            check(status == 1 and output['outcome'] == 'not-reproduced', f'L1 upstream: {status} {output} {error}')
            requests, differing = upstream_sample(args, check, upstream, signer)
            print(f"ok L1 upstream {output['revision']}: the candidate does not reproduce; "
                  f"{len(differing)} of {requests} responses to 500 generated cases differ from the pin harness "
                  f"({time.monotonic() - started:.1f} s)")
            checks += 1

        if node:
            started = time.monotonic()
            status, output, error = command('replay', '--level', 'L3', '--signer', signer, '--node', node,
                                            str(target), args.oracle, args.harness)
            saved = json.loads(target.read_text())
            evidence = saved['production']['replays'][-1] if 'production' in saved else {}
            check(status == 1 and output['outcome'] == 'not-reproduced',
                  f"L3: {status} {output} {error} {evidence.get('mempool')} {evidence.get('block')} "
                  f"{evidence.get('plan')}")
            check(output['classification'] == 'harness-fault', output)
            check(evidence['mempool']['result'] == reduced['expected']['verdict'], evidence['mempool'])
            # The planted harness still contradicts the node on the re-signed bytes.
            wrapped = campaign.execute(planted, evidence['requests'], 60)
            check(wrapped['responses'][-1]['ok']['result'] != evidence['mempool']['result'],
                  'the re-signed spend no longer triggers the planted fault')
            print(f"ok L3 pin: the node gives {evidence['mempool'].get('reason', 'acceptance')} in its mempool and "
                  f"{evidence['block'].get('reason', 'acceptance')} in a block, the planted harness answers "
                  f"{wrapped['responses'][-1]['ok']['result']} on the same bytes, and the candidate is a "
                  f"harness fault ({time.monotonic() - started:.1f} s)")
            checks += 1
            node_revision = (pathlib.Path(node) / 'node.revision').read_text().strip()
            if upstream and (pathlib.Path(upstream).parent / 'core.revision').read_text().strip() == node_revision:
                status, output, error = command('replay', '--level', 'L3', '--target', 'upstream', '--signer',
                                                str(pathlib.Path(upstream).with_name('core-signer')), '--node', node,
                                                str(target), args.oracle, upstream)
                check(status == 1 and output['outcome'] == 'not-reproduced', f'L3 upstream: {status} {output} {error}')
                check(output['classification'] == 'harness-fault', output)
                print(f"ok L3 upstream {output['revision']}: the node does not reproduce the candidate")
                checks += 1
            elif upstream:
                print('skip L3 upstream: the node build and the upstream harness name different commits')
            checks += l3_positives(args, check, signer, node)
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('oracle')
    parser.add_argument('harness')
    parser.add_argument('--signer', help='defaults to core-signer beside the harness')
    parser.add_argument('--node', help='a scripts/build_core_node.sh build directory at the pin')
    parser.add_argument('--upstream-harness', help='a scripts/build_core_harness.sh --revision build')
    args = parser.parse_args()
    args.oracle = str(pathlib.Path(args.oracle).resolve())
    args.harness = str(pathlib.Path(args.harness).resolve())
    upstream = str(pathlib.Path(args.upstream_harness).resolve()) if args.upstream_harness else None
    from test_campaign import check, wrapper
    started = time.monotonic()
    checks = stage4(args, check, wrapper, args.node and str(pathlib.Path(args.node).resolve()), upstream)
    print(f'{checks} cases, 0 failures ({time.monotonic() - started:.1f} s)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
