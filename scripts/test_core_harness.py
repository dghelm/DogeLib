"""Check that the Core harness keeps no adjusted time between requests.

Usage: python3 -I scripts/test_core_harness.py <dogelib-oracle> <core-oracle>

block.header_sequence sets Core's mock time and time offset, because
AcceptBlockHeader reads GetAdjustedTime. The test has two parts.

Verdicts: header-sequence requests at the limits of the adjusted-time domain,
each alone and all in one stream, with contextual checks between them. Each
response of the harness must be the same alone and in the stream, must have
the stated verdict, and must agree with the oracle.

State: after a success, a consensus rejection, a request error and a decoding
error, the harness-internal operation harness.time_state must report mock time
0 and time offset 0. Adjusted time 0 uses offset -1, so the test covers each
kind of exit at adjusted time 0 and at another value.
"""

import copy
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
from oracle_header_sequence import regtest_cases, EXPECTATIONS, key

INT64_MIN = -2**63
ADJUSTED_MAX = 2**63 - 1 - 7200


def check(condition, detail):
    """Keep checks active when Python optimizes bytecode."""
    if not condition:
        raise RuntimeError(detail)


def run(program, requests):
    data = ''.join(json.dumps(r) + '\n' for r in requests)
    done = subprocess.run([program], input=data, capture_output=True, text=True, timeout=300)
    check(done.returncode == 0, f'{program} exited with {done.returncode}: {done.stderr[-400:]}')
    lines = [json.loads(line) for line in done.stdout.splitlines() if line.strip()]
    check(len(lines) == len(requests), f'{program} gave {len(lines)} responses for {len(requests)} requests')
    return lines


def verdict(response):
    ok = response.get('ok')
    check(ok is not None, f'not a result: {response}')
    return ok['valid'], ok['reject_reason']


def main():
    check(len(sys.argv) == 3, 'usage: test_core_harness.py <dogelib-oracle> <core-oracle>')
    oracle, harness = sys.argv[1:]

    # An accepted regtest sequence of D83. Its header times are near 1296688702.
    accepted = next(r for r in regtest_cases()
                    if EXPECTATIONS[key(r)].get('valid') is True and r['headers'])

    def at(adjusted):
        req = copy.deepcopy(accepted)
        req['adjusted_time'] = adjusted
        return req

    empty = dict(op='block.header_sequence', network='mainnet', mode='base', adjusted_time=10**12,
                 checkpoints_enabled=False, index=[], failed_blocks=[], headers=[])
    # An unmined header with a predecessor outside the index. Core rejects it at
    # the proof-of-work check, which logs through error().
    unmined = dict(empty, headers=['01000000' + '11' * 32 + '00' * 32 + '00000000' + 'f0ff0f1e' + '00000000'])
    # A legacy header at mainnet height 371337, where AuxPoW is required
    # (validation.cpp:3073-3077). The check does not read the adjusted time.
    legacy = dict(op='block.contextual_check', network='mainnet',
                  bytes_hex='01000000' + '00' * 64 + '00000000' + 'ffff001b' + '00000000',
                  chain=[dict(height=371336 - i, time=1410464577 - 60 * i, bits=0x1b00ffff) for i in range(11)],
                  adjusted_time=1410464637, checkpoints_enabled=False, known_checkpoints=[])

    # (request, expected valid, expected reject reason), from D33 lines 3066-3119.
    cases = [
        (empty, True, None),
        (legacy, False, 'late-legacy-block'),
        (at(10**12), True, None),
        (at(INT64_MIN), False, 'time-too-new'),
        (legacy, False, 'late-legacy-block'),
        (at(ADJUSTED_MAX), True, None),
        # Mock time 0 would select the system clock, which accepts these headers.
        (at(0), False, 'time-too-new'),
        (legacy, False, 'late-legacy-block'),
        (unmined, False, 'high-hash'),
        (legacy, False, 'late-legacy-block'),
    ]
    requests = [c[0] for c in cases]
    stream = run(harness, requests)
    lean = run(oracle, requests)
    for i, (req, valid, reason) in enumerate(cases):
        alone = run(harness, [req])[0]
        check(alone == stream[i], f'case {i}: the harness response changes in the stream: {alone} != {stream[i]}')
        check(verdict(alone) == (valid, reason), f'case {i}: harness verdict {verdict(alone)}, expected {(valid, reason)}')
        check(verdict(lean[i]) == (valid, reason), f'case {i}: oracle verdict {verdict(lean[i])}, expected {(valid, reason)}')

    # (request, the kind of exit that the response must show).
    def kind(response):
        if 'ok' in response:
            return 'success' if response['ok']['valid'] else 'rejection'
        return response['error']['kind']

    exits = []
    for adjusted in (10**12, 0):
        exits += [
            (dict(empty, adjusted_time=adjusted), 'success'),
            (dict(unmined, adjusted_time=adjusted), 'rejection'),
            # The harness refuses the index after it has set the adjusted time.
            (dict(empty, adjusted_time=adjusted, index=[dict(unexpected=1)]), 'request'),
            # A header of one byte: Core's stream reader fails.
            (dict(empty, adjusted_time=adjusted, headers=['00']), 'read'),
        ]
    exits.append((at(INT64_MIN), 'rejection'))
    exits.append((at(0), 'rejection'))
    state = dict(op='harness.time_state')
    interleaved = [state]
    for req, _ in exits:
        interleaved += [req, state]
    responses = run(harness, interleaved)
    clean = dict(ok=dict(mock_time=0, time_offset=0))
    check({k: v for k, v in responses[0].items() if k != 'id'} == clean, f'initial state: {responses[0]}')
    for i, (req, expected) in enumerate(exits):
        answer, after = responses[1 + 2 * i], responses[2 + 2 * i]
        check(kind(answer) == expected, f'exit {i}: {answer}, expected {expected}')
        check({k: v for k, v in after.items() if k != 'id'} == clean,
              f'exit {i} ({expected}, adjusted time {req["adjusted_time"]}) left {after}')
    print(f'{len(cases)} verdict cases and {len(exits)} state checks, 0 failures')


if __name__ == '__main__':
    main()
