"""Enumerate the planted proposal's search space from design record 0009 §8.1."""

import itertools

from campaign_generator import transaction

ALPHABET = ('00', '51', '52', 'b3', '75', '69', '87', '0180')
LOCK_TIMES = (0, 1, 2, 499999999, 500000000)
SEQUENCES = (0xfffffffe, 0xffffffff)
SPACE_SIZE = sum(len(ALPHABET) ** n for n in range(1, 6)) * 10
EXPECTED = dict(property='RestrictsAcceptance',
                text='Design record 0009 §8.1: revised acceptance implies baseline acceptance.')


def script_case(plan, index):
    """Materialize the exact one-input context and instruction list of a script plan."""
    request = dict(id=f'proposal-{index}', op='script.verify_legacy', tx_hex=transaction(plan),
                   input_index=plan['n'], prevout_script_hex=''.join(plan['instructions']),
                   flags=plan['flags'], checker='transaction')
    return dict(input='proposal', source_index=index, case_index=index, plan=plan,
                expected=EXPECTED, requests=[request], signer=[])


def script_plan(instructions, lock_time=2, sequence=0xfffffffe):
    """Construct a script plan with the search's empty unlocking script and null outpoint."""
    return dict(mode='script', instructions=list(instructions), n=0, flags=0,
                tx=dict(version=1, lock_time=lock_time,
                        inputs=[dict(outpoint='00' * 32 + 'ffffffff', sequence=sequence, script_sig='')],
                        outputs=[]))


def parse_script(text):
    """Split hex script bytes into instructions, so that a push and its data form one element."""
    raw, out, i = bytes.fromhex(text.replace(' ', '')), [], 0
    while i < len(raw):
        op = raw[i]
        size = op if op <= 75 else 0
        if op in (76, 77, 78):
            width = {76: 1, 77: 2, 78: 4}[op]
            size = width + int.from_bytes(raw[i + 1:i + 1 + width], 'little')
        if i + 1 + size > len(raw):
            raise ValueError('script ends inside a push')
        out.append(raw[i:i + 1 + size].hex())
        i += 1 + size
    return out


def cases():
    """Enumerate every instruction tuple and context, shortest scripts first, without seeds."""
    index = 0
    for size in range(1, 6):
        for instructions in itertools.product(ALPHABET, repeat=size):
            for lock in LOCK_TIMES:
                for sequence in SEQUENCES:
                    yield script_case(script_plan(instructions, lock, sequence), index)
                    index += 1


def assess(cases, runs):
    """Check restriction of acceptance, and fail every response that is not a Script verdict.

    The harness slot runs proposal-replay, so a failure on that side names the side `revised`.
    """
    import campaign

    def side(name):
        return 'revised' if name == 'core' else name

    requests = [r for case in cases for r in campaign.case_requests(case)]
    errors = campaign.assess(requests, runs)
    if errors and errors[0][0] is None:
        kind, name, message, code = errors[0][1]
        return [(None, (kind, side(name), message, code, 'RestrictsAcceptance'))]
    results = []
    excluded = {i: r for i, r in errors if r[0] in ('crash', 'unsupported', 'refusal')}
    for i, _ in enumerate(cases):
        if i in excluded:
            kind, name, message, code = excluded[i]
            results.append((i, (kind, side(name), message, code, 'RestrictsAcceptance')))
            continue
        verdicts = {name: run['responses'][i].get('ok', {}).get('result') for name, run in runs.items()}
        # An error object or another result checks nothing, so it must not count as a pass.
        bad = [name for name, verdict in verdicts.items() if verdict not in ('accepted', 'rejected', 'unsupported')]
        unsupported = [name for name, verdict in verdicts.items() if verdict == 'unsupported']
        if unsupported and not bad:
            results.append((i, ('unsupported', 'both' if len(unsupported) == 2 else side(unsupported[0]),
                                'unsupported Script result', None, 'RestrictsAcceptance')))
        elif bad:
            results.append((i, ('crash', 'both' if len(bad) == 2 else side(bad[0]),
                                'response is not an accepted or rejected Script result', 'RESULT',
                                'RestrictsAcceptance')))
        elif verdicts['core'] == 'accepted' and verdicts['lean'] == 'rejected':
            results.append((i, ('verdict', 'revised', 'revised acceptance exceeds baseline',
                                'RestrictsAcceptance', 'RestrictsAcceptance')))
    return results
