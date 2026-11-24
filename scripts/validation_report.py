#!/usr/bin/env python3
"""Run the gates in AGENTS.md and preserve their commands, results and logs.

With --release MANIFEST the script runs the gates that the manifest lists under
`run`, in that order, and reports each gate under `not_run` as not run with the
manifest's reason. scripts/release_gates.json is the manifest of the release
workflow. The script refuses a manifest that leaves out a gate, that runs a gate
which needs the maintainer's node or its fixtures, or that runs a gate before the
gate that builds or fetches its inputs.
"""

import argparse
from collections import deque
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def read_gates(path):
    """Read the checks table, and reject ambiguous executable cells."""
    text = path.read_text()
    match = re.search(r'^\| Gate .*\| Command \| Exists \| In CI \|\n\|[^\n]+\n((?:\|[^\n]+\n)+)', text, re.M)
    if not match:
        raise ValueError('checks table not found')
    gates = []
    for row in match[1].splitlines():
        name, cell, exists, _ = [part.strip() for part in row.strip('|').split('|')]
        slug = re.sub(r'[^a-z0-9]+', '-', name.lower()).strip('-')
        spans = re.findall(r'`([^`]+)`', cell)
        manual = exists == 'Manual'
        if not manual and not spans:
            raise ValueError(f'{name}: command cell must have a code span')
        if any(g['slug'] == slug for g in gates):
            raise ValueError(f'duplicate gate: {slug}')
        gates.append(dict(slug=slug, name=name, command=None if manual else spans[0], description=cell,
                          exists=exists))
    return gates


# A gate whose cells match this pattern needs the maintainer's node, the fixtures
# fetched from it, or the Core pass. A GitHub runner cannot run it.
NODE_ONLY = re.compile(r"\bthe node\b|maintainer's node|build/core-node|build/core-pass|build/ranges/|"
                       r"build/range-runs|range-10001-145000|genesis-145000|more than a day")

# Inputs that a gate reads, from its command and its Exists cell, and the command
# that makes each input. A release run must make an input in the same gate or in
# an earlier one.
INPUTS = {
    'release blocks': (r'build/mainnet-blocks|scripts/fetch_release_blocks\.py', r'scripts/fetch_release_blocks\.py'),
    'harness': (r'build/core-harness/|harness build', r'build_core_harness\.sh'),
    'overflow-trap harness': (r'core-oracle-trap|--trap-overflow', r'build_core_harness\.sh --trap-overflow'),
    'oracle': (r'\.lake/build/bin/dogelib-oracle|oracle build', r'lake build [^&]*\bdogelib-oracle\b'),
    'proposal oracle': (r'dogelib-proposal-oracle|proposal oracle build',
                        r'lake build [^&]*\bdogelib-proposal-oracle\b'),
    'proposal test oracle': (r'proposal-test-oracle', r'lake build [^&]*\bproposal-test-oracle\b'),
    'proposal-replay': (r'proposal-replay', r'^lake build --wfail\b'),
    # The kernel replay reads the .olean files of the library, which the build writes.
    'library build': (r'scripts/replay\.sh', r'^lake build --wfail\b'),
}


def node_only(gate):
    """Return whether a gate needs what only the maintainer's machine has."""
    return bool(NODE_ONLY.search(' '.join(filter(None, (gate['command'], gate['description'], gate['exists'])))))


def check_release(gates, manifest):
    """Return the ordered gates and the reasons of a release manifest, or raise ValueError."""
    if set(manifest) != {'run', 'not_run'}:
        raise ValueError('manifest must have exactly the keys run and not_run')
    run, not_run = manifest['run'], manifest['not_run']
    by_slug = {g['slug']: g for g in gates}
    listed = run + list(not_run)
    unknown = sorted(set(listed) - set(by_slug))
    if unknown:
        raise ValueError(f'manifest names unknown gates: {unknown}')
    if len(set(listed)) != len(listed):
        raise ValueError('manifest names a gate more than once')
    automated = {g['slug'] for g in gates if g['command'] is not None}
    if set(listed) != automated:
        raise ValueError(f'manifest must list each automated gate once: missing {sorted(automated - set(listed))}, '
                         f'manual {sorted(set(listed) - automated)}')
    made = set()
    for slug in run:
        gate = by_slug[slug]
        if node_only(gate):
            raise ValueError(f'{slug}: needs the maintainer\'s node or its fixtures, and cannot run on a runner')
        text = gate['command'] + ' ' + gate['exists']
        made |= {name for name, (_, maker) in INPUTS.items() if re.search(maker, gate['command'])}
        missing = sorted(name for name, (reader, _) in INPUTS.items() if re.search(reader, text) and name not in made)
        if missing:
            raise ValueError(f'{slug}: runs before a gate that makes its inputs: {missing}')
    if any(not isinstance(reason, str) or not reason.strip() for reason in not_run.values()):
        raise ValueError('each gate under not_run needs a reason')
    return run, not_run


def capture(command):
    """Capture metadata without turning a missing tool into a passing check."""
    try:
        result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, errors='replace')
        return f'$ {shlex.join(command)}\nexit {result.returncode}\n{result.stdout.strip()}'
    except OSError as error:
        return f'$ {shlex.join(command)}\nunavailable: {error}'


def fence(text):
    """Keep arbitrary command output inside a Markdown code block."""
    marker = '`' * max(3, max((len(s) + 1 for s in re.findall(r'`+', text)), default=3))
    return f'{marker}text\n{text}\n{marker}\n'


def write_report(path, metadata, gates, results, dirty, final_status=None):
    """Replace the report after each completed gate."""
    lines = ['**Dirty working tree.**' if dirty else 'Clean working tree.', '',
             '# Validation report', '', fence(metadata),
             'The summaries contain the last 20 output lines of each command.',
             'A zero exit status records command success, not a proof or a manual review.',
             'The Writing gate is advisory. Its output can contain findings with exit status zero.',
             'Build checks the root package. Refinement checks the separate package under Refinement/.',
             '', '## Core harness stamp', '']
    stamp = ROOT / 'build/core-harness/core.stamp'
    lines.append(fence(stamp.read_text() if stamp.exists() else 'not available'))
    lines.append('The stamp describes existing Core libraries. It does not establish that this run built the harness.\n')
    if final_status is not None:
        lines += ['## Final tree status', '', fence(final_status),
                  'Compare this status with the initial tree-status log. A gate may have changed the tree.', '']
    for gate in gates:
        result = results.get(gate['slug'], dict(status='not run', reason='not selected or not reached'))
        lines += [f"## {gate['name']}", '', f"Status: **{result['status']}**", '']
        lines.append(fence(result.get('command') or gate['command'] or gate['description']))
        if 'reason' in result:
            lines.append(result['reason'] + '\n')
        if 'log' in result:
            lines += [f"Full log: [{result['log']}]({result['log']})", '']
        if 'exit' in result:
            lines += [f"Exit status: {result['exit']}", '', f"Duration: {result['duration']:.3f} seconds", '',
                      fence(result['summary'])]
            if 'findings' in result:
                lines.append(f"Writing findings: {result['findings']} (advisory).\n")
    temp = path.with_suffix('.tmp')
    temp.write_text('\n'.join(lines))
    temp.replace(path)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--registry', type=Path, default=ROOT / 'AGENTS.md')
    parser.add_argument('--gates', help='comma-separated gate slugs (default: all)')
    parser.add_argument('--release', type=Path, metavar='MANIFEST',
                        help='run the gates of a release manifest, such as scripts/release_gates.json, in its order')
    parser.add_argument('--core-clone', type=Path)
    parser.add_argument('--output', type=Path, help='report path in an ignored directory')
    parser.add_argument('--list', action='store_true')
    args = parser.parse_args(argv)
    try:
        gates = read_gates(args.registry)
    except (ValueError, OSError) as error:
        parser.error(str(error))
    order, skipped = [g['slug'] for g in gates], {}
    if args.release:
        try:
            order, skipped = check_release(gates, json.loads(args.release.read_text()))
        except (ValueError, OSError, TypeError, AttributeError) as error:
            parser.error(f'{args.release}: {error}')
    selected = set(args.gates.split(',')) if args.gates else {g['slug'] for g in gates}
    unknown = selected - {g['slug'] for g in gates}
    if unknown:
        parser.error(f'unknown gates: {sorted(unknown)}')
    if args.list:
        for gate in gates:
            print(f"{gate['slug']}: {gate['command'] or gate['description']}")
        return 0
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    output = (args.output or ROOT / 'build/validation' / commit[:12] / 'report.md').resolve()
    # Reports and their logs must stay outside the tracked source tree.
    ignored = subprocess.run(['git', 'check-ignore', '-q', str(output)], cwd=ROOT).returncode == 0
    tracked = subprocess.run(['git', 'ls-files', '--error-unmatch', str(output)], cwd=ROOT,
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
    if not ignored or tracked:
        parser.error('--output must name an untracked file in a gitignored directory')
    output.parent.mkdir(parents=True, exist_ok=True)
    logs = output.parent / (output.stem + '-logs')
    try:
        logs.mkdir(exist_ok=False)
    except FileExistsError:
        parser.error(f'log directory already exists: {logs}. Choose a different --output path.')
    status = subprocess.check_output(['git', 'status', '--porcelain=v1', '--untracked-files=all'], cwd=ROOT, text=True)
    dirty = bool(status)
    (logs / 'tree-status.txt').write_text(status)
    with (logs / 'tree.diff').open('w') as handle:
        subprocess.run(['git', 'diff', 'HEAD', '--binary'], cwd=ROOT, stdout=handle, check=True)
    sources = (ROOT / 'SOURCES.md').read_text()
    pin = re.search(r'\[Dogecoin Core\].*?`([0-9a-f]{40})`', sources)
    metadata = '\n'.join([
        f'Date (UTC): {datetime.now(timezone.utc).isoformat()}', f'DogeLib commit: {commit}',
        f'Tree: {"dirty" if dirty else "clean"}', f'Tree status: {logs.name}/tree-status.txt',
        f'Tracked diff: {logs.name}/tree.diff', 'Untracked files are listed but are not included in the diff.',
        f'Invocation: {shlex.join([sys.executable, "-I", *sys.argv])}', f'Working directory: {ROOT}', 'Shell wrapper: bash -o pipefail -c <command>',
        f'Registry: {args.registry.resolve()}',
        f'Registry SHA-256: {hashlib.sha256(args.registry.read_bytes()).hexdigest()}',
        f'Release manifest: {args.release.resolve() if args.release else "none"}',
        *([f'Release manifest SHA-256: {hashlib.sha256(args.release.read_bytes()).hexdigest()}']
          if args.release else []),
        f'lean-toolchain: {(ROOT / "lean-toolchain").read_text().strip()}',
        f'Core pin: {pin[1] if pin else "not found"}', f'Core clone: {args.core_clone}',
        f'Python: {sys.version}', f'OS: {platform.platform()}', f'Machine: {platform.machine()}',
        f'CPU affinity: {sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else "unavailable"}',
        f'Niceness: {os.getpriority(os.PRIO_PROCESS, 0) if hasattr(os, "getpriority") else "unavailable"}',
        f'CC: {os.environ.get("CC", "gcc")}',
        f'LEAN_CC: {os.environ.get("LEAN_CC", "toolchain default")}', f'CXX: {os.environ.get("CXX", "g++")}',
        f'JOBS: {os.environ.get("JOBS", "8 (harness default)")}',
        *[capture(c) for c in [['lean', '--version'], ['lake', 'env', 'lean', '--print-prefix'],
                              ['lake', 'env', 'cc', '--version'], ['lake', 'env', 'leanc', '--version'],
                              [os.environ.get('CC', 'gcc'), '--version'],
                              [os.environ.get('CXX', 'g++'), '--version']]]])
    results = {}
    failed = False
    for slug, reason in skipped.items():
        if slug in selected:
            results[slug] = dict(status='not run', reason=f'Not in the release run: {reason}')
    write_report(output, metadata, gates, results, dirty)
    by_slug = {g['slug']: g for g in gates}
    for slug in order:
        gate = by_slug[slug]
        if slug not in selected:
            continue
        command = gate['command']
        reason = None
        if command is None:
            reason = 'Manual review requires a reviewer.'
        elif '<dogecoin-git-clone>' in command and args.core_clone:
            command = command.replace('<dogecoin-git-clone>', shlex.quote(str(args.core_clone.resolve())))
        if command and re.search(r'<[^<>]+>', command):
            reason = 'Unresolved placeholder. Supply --core-clone for the Core comparison.'
        if reason:
            results[slug] = dict(status='not run', reason=reason, command=command)
            write_report(output, metadata, gates, results, dirty)
            continue
        print(f'Running {slug}: {command}', flush=True)
        log = logs / f'{slug}.log'
        start = time.monotonic()
        results[slug] = dict(status='running/incomplete', command=command,
                             log=f'{logs.name}/{log.name}',
                             reason='Gate launch began. No completed result has been recorded.')
        write_report(output, metadata, gates, results, dirty)
        interrupted = False
        try:
            with log.open('w') as handle:
                process = subprocess.Popen(['bash', '-o', 'pipefail', '-c', command], cwd=ROOT,
                                           stdout=handle, stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    code = process.wait()
                except KeyboardInterrupt:
                    interrupted = True
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        pass
                    finally:
                        # A child can survive after the shell exits.
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                    code = process.wait()
        except OSError as error:
            with log.open('a') as handle:
                handle.write(f'Runner error: {error}\n')
            code = 127
        with log.open(errors='replace') as handle:
            summary = ''.join(deque(handle, maxlen=20)).rstrip()
        results[slug] = dict(status='interrupted' if interrupted else ('passed' if code == 0 else 'failed'), command=command,
                             exit=code, duration=time.monotonic() - start,
                             log=f'{logs.name}/{log.name}', summary=summary)
        if slug == 'writing':
            count = re.search(r'(\d+) writing finding\(s\)', summary)
            results[slug]['findings'] = count[1] if count else ('0' if 'No writing findings.' in summary else 'unavailable')
        failed |= code != 0
        write_report(output, metadata, gates, results, dirty)
        print(f'{slug}: exit {code}', flush=True)
        if interrupted:
            return 130
    final_status = subprocess.check_output(
        ['git', 'status', '--porcelain=v1', '--untracked-files=all'], cwd=ROOT, text=True)
    (logs / 'tree-status-final.txt').write_text(final_status)
    with (logs / 'tree-final.diff').open('w') as handle:
        subprocess.run(['git', 'diff', 'HEAD', '--binary'], cwd=ROOT, stdout=handle, check=True)
    tree_changed = (final_status != status or
                    (logs / 'tree.diff').read_bytes() != (logs / 'tree-final.diff').read_bytes())
    final_note = ('Tree status or tracked diff changed during the run.\n' if tree_changed else
                  'Tree status and tracked diff at completion match their initial values.\n')
    final_note += f'Final tracked diff: {logs.name}/tree-final.diff\n' + final_status
    write_report(output, metadata, gates, results, dirty, final_note)
    print(f'Report: {output}')
    return int(failed)


def interrupt(signum, frame):
    """Use the same cleanup path for termination and keyboard interruption."""
    raise KeyboardInterrupt


if __name__ == '__main__':
    signal.signal(signal.SIGTERM, interrupt)
    sys.exit(main())
