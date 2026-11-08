"""Reduce a saved campaign failure by changing its construction plan.

Design record 0009, section 7.4, sets the rules.
A candidate plan replaces the current plan when the campaign's own run path, on that candidate alone, saves a failure with the same property, class and failing side.
The run path signs generated candidates in their own mode: a preserve plan is signed after its mutations, and a commitment plan is signed before them.
"""

import argparse
import copy
import json
import pathlib
import shlex
import shutil
import sys
import tempfile

import campaign

STEPS = ('elements', 'inputs-outputs', 'numbers', 'flags', 'hash-type-selector', 'other-scripts')
# The template's CLTV operand is 1,000,000, and 500,000,000 separates heights from times (C4).
LOCK_CLASSES = ((0, 1000000, 0), (1000000, 500000000, 1000000), (500000000, 1 << 32, 500000000))
FINAL = 0xffffffff
# VerifyScript asserts that WITNESS implies P2SH and that CLEANSTACK implies both (C7).
P2SH, CLEANSTACK, WITNESS = 1, 256, 2048


def condition(record):
    """The failure condition of section 7.4."""
    return record['property'], record['class'], record['failing_side']


def in_assertion_domain(flags):
    """Keep a flag combination that the harness can run without an assertion."""
    return not ((flags & WITNESS and not flags & P2SH) or
                (flags & CLEANSTACK and not (flags & P2SH and flags & WITNESS)))


def elements(plan):
    """The removable elements: instructions of a script plan, or mutations of a generated plan."""
    if plan['mode'] == 'script':
        return list(range(len(plan['instructions'])))
    items = [('mutation', i) for i in range(len(plan['mutations']))]
    if plan.get('signature_mutation', 'none') != 'none':
        items.append(('signature', 0))
    return items


def without(plan, removed):
    """Remove the chosen elements of `elements(plan)`."""
    p = copy.deepcopy(plan)
    items = elements(plan)
    gone = {items[i] for i in removed}
    if p['mode'] == 'script':
        p['instructions'] = [x for i, x in enumerate(plan['instructions']) if i not in gone]
    else:
        p['mutations'] = [m for i, m in enumerate(plan['mutations']) if ('mutation', i) not in gone]
        if ('signature', 0) in gone:
            p['signature_mutation'] = 'none'
    return p, f'remove elements {sorted(removed)}'


def step_elements(plan):
    """Step 1: single elements, then adjacent pairs, then halves."""
    count = len(elements(plan))
    for i in range(count):
        yield without(plan, {i})
    for i in range(count - 1):
        yield without(plan, {i, i + 1})
    if count >= 4:
        half = count // 2
        yield without(plan, set(range(half)))
        yield without(plan, set(range(half, count)))


def step_inputs_outputs(plan):
    """Step 2: remove other inputs and outputs, then move input n towards position 0."""
    n = plan['n']
    for j in range(len(plan['tx']['inputs'])):
        if j != n:
            p = copy.deepcopy(plan)
            del p['tx']['inputs'][j]
            p['n'] = n - 1 if j < n else n
            yield p, f'remove input {j}'
    for j in range(len(plan['tx']['outputs'])):
        p = copy.deepcopy(plan)
        del p['tx']['outputs'][j]
        yield p, f'remove output {j}'
    for target in sorted({0, n - 1}):
        if 0 <= target < n:
            p = copy.deepcopy(plan)
            p['tx']['inputs'].insert(target, p['tx']['inputs'].pop(n))
            p['n'] = target
            yield p, f'move input {n} to {target}'


def step_numbers(plan):
    """Step 3: simpler values of the same boundary class, and push values of 0 in a script plan."""
    if plan['mode'] == 'script':
        for i, instruction in enumerate(plan['instructions']):
            # Data pushes, OP_1NEGATE and OP_1 to OP_16 push a value. OP_0 pushes the number 0.
            op = int(instruction[:2], 16)
            if instruction != '00' and (op <= 0x4f or 0x51 <= op <= 0x60):
                p = copy.deepcopy(plan)
                p['instructions'][i] = '00'
                yield p, f'push value 0 at instruction {i}'
    tx = plan['tx']
    if tx['version'] != 1:
        p = copy.deepcopy(plan)
        p['tx']['version'] = 1
        yield p, 'version 1'
    lock = tx['lock_time']
    for low, high, simple in LOCK_CLASSES:
        if low <= lock < high and lock != simple:
            p = copy.deepcopy(plan)
            p['tx']['lock_time'] = simple
            yield p, f'lock time {simple}'
    for j, item in enumerate(tx['inputs']):
        if item['sequence'] not in (0, FINAL):
            p = copy.deepcopy(plan)
            p['tx']['inputs'][j]['sequence'] = 0
            yield p, f'sequence 0 on input {j}'
    for j, item in enumerate(tx['outputs']):
        if item['value'] != 0:
            p = copy.deepcopy(plan)
            p['tx']['outputs'][j]['value'] = 0
            yield p, f'value 0 on output {j}'


def step_flags(plan):
    """Step 4: clear each flag, inside the assertion domain of C7."""
    bit = 1
    while bit <= plan['flags']:
        if plan['flags'] & bit and in_assertion_domain(plan['flags'] & ~bit):
            p = copy.deepcopy(plan)
            p['flags'] &= ~bit
            yield p, f'clear flag {bit}'
        bit <<= 1


def step_hash_type_selector(plan):
    """Step 5: hash type ALL, then the selector 01 or the empty push."""
    if plan['mode'] == 'script':
        return
    types = plan['hash_types']
    if any(h != 1 for h in types):
        p = copy.deepcopy(plan)
        p['hash_types'] = [1] * len(types)
        yield p, 'hash type ALL on every signature'
        for i, h in enumerate(types):
            if h != 1 and len(types) > 1:
                p = copy.deepcopy(plan)
                p['hash_types'][i] = 1
                yield p, f'hash type ALL on signature {i}'
    for selector in ('01', ''):
        if plan['selector'] != selector:
            p = copy.deepcopy(plan)
            p['selector'] = selector
            yield p, f'selector {selector or "empty"}'


def step_other_scripts(plan):
    """Step 6: shorten other scripts byte by byte."""
    tx = plan['tx']
    places = [('inputs', j, 'script_sig') for j in range(len(tx['inputs'])) if j != plan['n']]
    places += [('outputs', j, 'script') for j in range(len(tx['outputs']))]
    for group, j, key in places:
        raw = tx[group][j][key]
        for k in range(0, len(raw), 2):
            p = copy.deepcopy(plan)
            p['tx'][group][j][key] = raw[:k] + raw[k + 2:]
            yield p, f'remove byte {k // 2} of {group[:-1]} {j} script'


STEP_FUNCTIONS = dict(zip(STEPS, (step_elements, step_inputs_outputs, step_numbers, step_flags,
                                  step_hash_type_selector, step_other_scripts)))


def valid(plan):
    """Reject a candidate that the plan's own construction cannot build."""
    if not 0 <= plan['n'] < len(plan['tx']['inputs']):
        return False
    if plan['mode'] == 'script':
        return True
    from campaign_generator import describe_mutations, signing_requests
    try:
        describe_mutations(plan)
        signing_requests(plan, 'reduce-check')
    except (IndexError, KeyError, ValueError):
        return False
    return True


class Reducer:
    """Evaluate candidates through `campaign.run_campaign`, with a cache and a limit."""

    def __init__(self, record, programs, workdir, limit):
        self.record, self.programs, self.workdir, self.limit = record, programs, workdir, limit
        self.target = condition(record)
        self.proposal = record['plan']['mode'] == 'proposal'
        self.candidates = 0
        self.cache = {}
        self.revisions = None
        arguments = record.get('program_arguments', {}).get('core', [])
        self.variant = arguments[1] if self.proposal and len(arguments) > 1 else 'faulty'

    def evaluate(self, plan):
        """The saved record and its file name when the candidate keeps the failure condition, else None."""
        key = campaign.canonical(plan)
        if key in self.cache:
            return self.cache[key]
        self.candidates += 1
        out = self.workdir / f'candidate-{self.candidates}'
        timeout = self.record['timeout']
        args = argparse.Namespace(campaign='proposal' if self.proposal else 'generated', variant=self.variant,
                                  seed=self.record['seed'], cases=1, seconds=max(60.0, 10 * timeout),
                                  timeout=timeout, batch_size=1, inputs=['generated'], output=str(out),
                                  **self.programs)
        if self.proposal:
            from campaign_proposal import script_case
            case = script_case(copy.deepcopy(plan), 0)
        else:
            case = dict(plan=copy.deepcopy(plan))
        summary = campaign.run_campaign(args, [case], self.revisions)
        if self.revisions is None:
            self.revisions = summary['revisions']
        found = None
        for path in summary['saved']:
            saved = json.loads(pathlib.Path(path).read_text())
            if condition(saved) == self.target:
                found = saved, pathlib.Path(path).name
                break
        self.cache[key] = found
        return found

    def run(self, plan):
        """Apply the steps in order until a complete pass keeps no change, or the limit ends it."""
        current = self.evaluate(plan)
        if current is None:
            raise ValueError('the stored plan does not reproduce the failure condition')
        trace = []
        while True:
            changed = False
            for name in STEPS:
                progress = True
                while progress:
                    progress = False
                    for candidate, change in STEP_FUNCTIONS[name](plan):
                        if candidate == plan or not valid(candidate):
                            continue
                        if campaign.canonical(candidate) not in self.cache and self.candidates >= self.limit:
                            return plan, current, trace, 'budget'
                        found = self.evaluate(candidate)
                        if found is not None:
                            plan, current, progress, changed = candidate, found, True, True
                            trace.append(dict(step=STEPS.index(name) + 1, name=name, change=change,
                                              candidates=self.candidates, elements=len(elements(plan))))
                            break
            if not changed:
                return plan, current, trace, 'minimal'


def stored_plan(record):
    """The construction plan of a single-case saved failure."""
    inputs = record.get('plan', {}).get('inputs', [])
    if record.get('plan', {}).get('mode') not in ('proposal', 'generated') or len(inputs) != 1 or 'plan' not in inputs[0]:
        raise ValueError('the reducer needs a saved failure of one generated or proposal case')
    return copy.deepcopy(inputs[0]['plan'])


def reduce_failure(path, oracle, harness, signer=None, limit=2000):
    """Reduce one saved failure and write the result beside its run, under reduced/."""
    path = pathlib.Path(path).resolve()
    record = json.loads(path.read_text())
    if record.get('format') != campaign.FORMAT:
        raise ValueError('unsupported saved-failure format')
    plan = stored_plan(record)
    if record['plan']['mode'] == 'generated' and not signer:
        raise ValueError('a generated failure needs the signer argument')
    base = campaign.ROOT / 'build/campaign'
    base.mkdir(parents=True, exist_ok=True)
    workdir = pathlib.Path(tempfile.mkdtemp(prefix='reduce-', dir=base))
    try:
        reducer = Reducer(record, dict(oracle=oracle, harness=harness, signer=signer), workdir, limit)
        plan, (result, name), trace, label = reducer.run(plan)
        output = path.parent.parent / 'reduced'
        output.mkdir(exist_ok=True)
        target = output / name
        for key in ('campaign', 'seed', 'case_index', 'budget'):
            result[key] = record[key]
        result['reduced_from'] = path.name
        result['reduction'] = dict(label=label, candidates=reducer.candidates, limit=limit, steps=trace)
        replay = [sys.executable, '-I', str(campaign.ROOT / 'scripts/campaign.py'), 'replay', str(target), oracle, harness]
        result['replay'] = shlex.join(replay) + (' --signer ' + shlex.quote(signer) if result['failing_side'] == 'signer' else '')
        target.write_text(json.dumps(result, indent=2) + '\n')
        return target, result
    finally:
        shutil.rmtree(workdir, ignore_errors=True)


def reduce_command(args):
    """The `campaign.py reduce` command: print the label and counts, never requests."""
    target, result = reduce_failure(args.failure, args.oracle, args.harness, args.signer, args.max_candidates)
    summary = dict(output=str(target), reduced_from=result['reduced_from'], label=result['reduction']['label'],
                   candidates=result['reduction']['candidates'], changes=len(result['reduction']['steps']),
                   property=result['property'], failing_side=result['failing_side'], **{'class': result['class']})
    print(json.dumps(summary))
    return 0
