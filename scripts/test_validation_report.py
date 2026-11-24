#!/usr/bin/env python3
"""Check report evidence, gate execution and the repository's registry."""

import importlib.util
import json
import os
import re
import shlex
import signal
import threading
import time
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('validation_report', ROOT / 'scripts/validation_report.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def registry(rows):
    return ('| Gate | Command | Exists | In CI |\n| --- | --- | --- | --- |\n' +
            ''.join(f'| {name} | {command} | {exists} | No |\n' for name, command, exists in rows))


def pinned_directories(text):
    """Return the directories of each `(cd DIR && sha256sum -c SHA256SUMS)` in order."""
    return re.findall(r'\(cd (\S+) && sha256sum -c SHA256SUMS\)', text)


class WorkflowDependencies(unittest.TestCase):
    def test_core_packages_match_validation(self):
        packages = {}
        # The jobs of workflow core install their packages in the shared setup action.
        for workflow, path in (('core', '.github/actions/core-setup/action.yml'),
                               ('validation', '.github/workflows/validation.yml')):
            text = (ROOT / path).read_text()
            installs = [shlex.split(line.strip()) for line in text.splitlines()
                        if line.strip().startswith('sudo apt-get install ')]
            self.assertEqual(len(installs), 1, workflow)
            packages[workflow] = {word for word in installs[0][3:] if not word.startswith('-')}
            self.assertIn('libevent-dev', packages[workflow], workflow)
        self.assertEqual(packages['core'], packages['validation'])

    def test_ci_pinned_vectors_match_registry(self):
        workflow = (ROOT / '.github/workflows/ci.yml').read_text()
        step = re.search(r'- name: pinned vectors\n(?:.*\n)*?        run: \|\n((?: {10}.*\n)+)', workflow)
        self.assertIsNotNone(step)
        gates = {g['slug']: g for g in runner.read_gates(ROOT / 'AGENTS.md')}
        registry_dirs = pinned_directories(gates['pinned-vectors']['command'])
        self.assertEqual(pinned_directories(step[1]), registry_dirs)
        # Every committed SHA256SUMS file is in the list.
        sums = sorted(str(p.parent.relative_to(ROOT)) for p in (ROOT / 'tests').rglob('SHA256SUMS'))
        self.assertEqual(sorted(registry_dirs), sums)

    def test_validation_workflow_runs_release_manifest(self):
        text = (ROOT / '.github/workflows/validation.yml').read_text()
        self.assertIn('scripts/validation_report.py --release scripts/release_gates.json', text)


class Release(unittest.TestCase):
    def setUp(self):
        self.gates = runner.read_gates(ROOT / 'AGENTS.md')
        self.manifest = json.loads((ROOT / 'scripts/release_gates.json').read_text())

    def test_real_manifest(self):
        run, not_run = runner.check_release(self.gates, self.manifest)
        node_only = {g['slug'] for g in self.gates if g['command'] and runner.node_only(g)}
        self.assertEqual(node_only, {
            'campaign-regtest-replay', 'version-bits-walk', 'impact-runs-on-the-ranges', 'impact-run-to-145-000',
            'mainnet-replay-to-145-000', 'snapshot-range-s', 'core-pass', 'mainnet-range'})
        self.assertLessEqual(node_only, set(not_run))
        self.assertIn('subsidy-seeds', not_run)
        self.assertFalse(node_only & set(run))

    def test_node_only_row_cannot_be_selected(self):
        for gate in self.gates:
            if gate['command'] and runner.node_only(gate):
                manifest = dict(run=self.manifest['run'] + [gate['slug']],
                                not_run={k: v for k, v in self.manifest['not_run'].items() if k != gate['slug']})
                with self.assertRaisesRegex(ValueError, 'node', msg=gate['slug']):
                    runner.check_release(self.gates, manifest)

    def test_order_follows_inputs(self):
        run = self.manifest['run']
        for consumer, maker in (('snapshot-range-short-form', 'mainnet-block-ranges'),
                                ('core-pass-self-test', 'core-comparison'),
                                ('core-harness-state', 'core-comparison'),
                                ('impact-tools-self-test', 'proposal-oracle'),
                                ('comparator-self-test', 'proposal-oracle'),
                                ('campaign-proposal-search', 'build'),
                                ('kernel-replay', 'build')):
            moved = [s for s in run if s != consumer]
            moved.insert(moved.index(maker), consumer)
            with self.assertRaisesRegex(ValueError, 'inputs', msg=consumer):
                runner.check_release(self.gates, dict(run=moved, not_run=self.manifest['not_run']))

    def test_manifest_must_list_each_gate(self):
        bad = [dict(run=self.manifest['run'][1:], not_run=self.manifest['not_run']),
               dict(run=self.manifest['run'] + ['build'], not_run=self.manifest['not_run']),
               dict(run=self.manifest['run'] + ['soundness-review'], not_run=self.manifest['not_run']),
               dict(run=self.manifest['run'] + ['no-such-gate'], not_run=self.manifest['not_run']),
               dict(run=self.manifest['run'], not_run={**self.manifest['not_run'], 'subsidy-seeds': ' '}),
               dict(run=self.manifest['run'])]
        for manifest in bad:
            with self.assertRaises(ValueError):
                runner.check_release(self.gates, manifest)


class Reports(unittest.TestCase):
    def setUp(self):
        (ROOT / '.lane').mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=ROOT / '.lane')
        self.root = Path(self.temp.name)
        self.original_root = runner.ROOT
        runner.ROOT = self.root
        for name, text in {'.gitignore': 'build/\n', 'lean-toolchain': 'fixture-toolchain\n',
                           'SOURCES.md': '[Dogecoin Core](fixture) | `' + 'a' * 40 + '`\n'}.items():
            (self.root / name).write_text(text)
        self.git('init', '-q')
        self.git('add', '.')
        self.git('-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-qm', 'fixture')
        self.original_capture = runner.capture
        runner.capture = lambda command: 'fixture metadata: ' + ' '.join(command)

    def tearDown(self):
        runner.ROOT = self.original_root
        runner.capture = self.original_capture
        self.temp.cleanup()

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True)

    def run_report(self, rows, *args):
        path = self.root / 'AGENTS.md'
        path.write_text(registry(rows))
        output = self.root / 'build/report.md'
        code = runner.main(['--registry', str(path), '--output', str(output), *args])
        return code, output.read_text()

    def test_failure_continues_and_preserves_logs(self):
        code, text = self.run_report([
            ('Pass', '`printf "first\\n"`', 'Yes'),
            ('Fail', '`printf "failure\\n"; exit 7`', 'Yes'),
            ('After', '`printf "after\\n"`', 'Yes')])
        self.assertEqual(code, 1)
        self.assertIn('Exit status: 7', text)
        self.assertIn('Duration:', text)
        self.assertIn('after\n', text)
        self.assertEqual((self.root / 'build/report-logs/fail.log').read_text(), 'failure\n')
        self.assertTrue(text.startswith('**Dirty working tree.**'))
        self.assertIn('?? AGENTS.md', (self.root / 'build/report-logs/tree-status.txt').read_text())

    def test_manual_placeholder_and_subset(self):
        code, text = self.run_report([
            ('Manual review', 'Review sources', 'Manual'),
            ('Missing', '`echo <unknown>`', 'Yes'),
            ('Skip', '`exit 5`', 'Yes')], '--gates', 'manual-review,missing')
        self.assertEqual(code, 0)
        self.assertEqual(text.count('**not run**'), 3)
        self.assertIn('Unresolved placeholder', text)
        self.assertNotIn('**passed**', text)

    def test_release_order_and_reasons(self):
        manifest = self.root / 'build/manifest.json'
        manifest.parent.mkdir()
        manifest.write_text(json.dumps(dict(run=['third', 'first'], not_run={'second': 'Needs a fixture.'})))
        code, text = self.run_report([
            ('First', '`echo first >> build/order`', 'Yes'),
            ('Second', '`exit 9`', 'Yes'),
            ('Third', '`echo third >> build/order`', 'Yes'),
            ('Manual review', 'Review sources', 'Manual')], '--release', str(manifest))
        self.assertEqual(code, 0)
        self.assertEqual((self.root / 'build/order').read_text(), 'third\nfirst\n')
        self.assertIn('Not in the release run: Needs a fixture.', text)
        self.assertEqual(text.count('**passed**'), 2)
        self.assertEqual(text.count('**not run**'), 2)
        self.assertIn('Release manifest SHA-256:', text)

    def test_release_refuses_node_only_gate(self):
        manifest = self.root / 'build/manifest.json'
        manifest.parent.mkdir()
        manifest.write_text(json.dumps(dict(run=['node'], not_run={})))
        with self.assertRaises(SystemExit) as error:
            self.run_report([('Node', '`fetch --from the node`', 'Yes')], '--release', str(manifest))
        self.assertEqual(error.exception.code, 2)

    def test_core_path_is_shell_quoted(self):
        path = self.root / 'clone with spaces; exit 8'
        code, text = self.run_report([('Core', '`printf "%s" <dogecoin-git-clone>`', 'Yes')],
                                     '--core-clone', str(path))
        self.assertEqual(code, 0)
        self.assertEqual((self.root / 'build/report-logs/core.log').read_text(), str(path))
        self.assertIn('**passed**', text)

    def test_clean_tree_and_stamp(self):
        (self.root / 'AGENTS.md').write_text(registry([('Pass', '`true`', 'Yes')]))
        self.git('add', '.')
        self.git('-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-qm', 'registry')
        stamp = self.root / 'build/core-harness/core.stamp'
        stamp.parent.mkdir(parents=True)
        stamp.write_text('pin ' + 'a' * 40 + '\ncxx fixture compiler\n')
        code = runner.main(['--output', str(self.root / 'build/report.md')])
        text = (self.root / 'build/report.md').read_text()
        self.assertEqual(code, 0)
        self.assertTrue(text.startswith('Clean working tree.'))
        self.assertIn('cxx fixture compiler', text)
        self.assertIn(self.git('rev-parse', 'HEAD').strip(), text)

    def test_interruption_stops_descendants_and_keeps_evidence(self):
        child_file = self.root / 'child.pid'

        def send_interrupt():
            for _ in range(500):
                if child_file.exists():
                    os.kill(os.getpid(), signal.SIGINT)
                    return
                time.sleep(0.01)

        sender = threading.Thread(target=send_interrupt)
        sender.start()
        try:
            code, text = self.run_report([
                ('Interrupted', '`sleep 30 & echo $! > child.pid; echo started; wait`', 'Yes'),
                ('After', '`true`', 'Yes')])
        finally:
            sender.join()
        self.assertEqual(code, 130)
        self.assertIn('**interrupted**', text)
        self.assertIn('Exit status:', text)
        self.assertIn('Duration:', text)
        self.assertIn('Full log:', text)
        self.assertIn('started', text)
        self.assertIn('**not run**', text)
        pid = child_file.read_text().strip()
        state = subprocess.run(['ps', '-p', pid, '-o', 'stat='], capture_output=True, text=True).stdout.strip()
        self.assertTrue(not state or state.startswith('Z'), state)

    def test_running_checkpoint(self):
        code, _ = self.run_report([('Snapshot', '`cp build/report.md build/checkpoint.md`', 'Yes')])
        self.assertEqual(code, 0)
        checkpoint = (self.root / 'build/checkpoint.md').read_text()
        self.assertIn('**running/incomplete**', checkpoint)
        self.assertIn('snapshot.log', checkpoint)
        self.assertNotIn('**passed**', checkpoint)

    def test_repeated_output_has_clear_error(self):
        self.run_report([('Pass', '`true`', 'Yes')])
        with self.assertRaises(SystemExit) as error:
            runner.main(['--output', str(self.root / 'build/report.md')])
        self.assertEqual(error.exception.code, 2)

    def test_gate_tree_change_is_recorded(self):
        code, text = self.run_report([('Change', '`echo changed >> lean-toolchain`', 'Yes')])
        self.assertEqual(code, 0)
        self.assertIn('Tree status or tracked diff changed during the run.', text)
        self.assertIn('M lean-toolchain', (self.root / 'build/report-logs/tree-status-final.txt').read_text())
        self.assertIn('+changed', (self.root / 'build/report-logs/tree-final.diff').read_text())

    def test_rejects_nonignored_output(self):
        with self.assertRaises(SystemExit) as error:
            runner.main(['--registry', str(ROOT / 'AGENTS.md'), '--output', str(self.root / 'report.md')])
        self.assertEqual(error.exception.code, 2)

    def test_rejects_missing_command(self):
        path = self.root / 'AGENTS.md'
        path.write_text(registry([('Broken', 'echo no code span', 'Yes')]))
        with self.assertRaises(ValueError):
            runner.read_gates(path)

    def test_real_registry(self):
        gates = runner.read_gates(ROOT / 'AGENTS.md')
        expected = {
            'build': 'lake build --wfail',
            'declaration-check': 'lake exe check-decls',
            'test-declaration-check': 'lake exe check-decls --scope ProposalExamples ProposalExamples ProposalExamples.Proofs ProposalExamples.Exports',
            'import-boundaries': 'lake env lean --run scripts/CheckRefinementImports.lean',
            'import-boundary-self-test': 'bash scripts/test_import_boundaries.sh',
            'rust-known-answers': 'cargo +nightly-2026-09-17 test --locked --manifest-path Refinement/Rust/Cargo.toml --jobs 4',
            'rust-extraction-freshness': 'Refinement/Rust/regenerate.sh --check',
            'declaration-check-self-test': 'bash scripts/test_check_decls.sh',
            'kernel-replay': 'REPLAY_JOBS=2 bash scripts/replay.sh && REPLAY_JOBS=2 bash scripts/replay.sh tests/ProposalExamples',
            'kernel-replay-self-test': 'bash scripts/test_replay.sh',
            'source-and-coverage-review': None,
            'conformance': 'lake test',
            'pinned-vectors': '(cd tests/cryptography/secp256k1 && sha256sum -c SHA256SUMS) && '
                              '(cd tests/cryptography/ripemd160 && sha256sum -c SHA256SUMS) && '
                              '(cd tests/cryptography/sha1/cavp && sha256sum -c SHA256SUMS) && '
                              '(cd tests/cryptography/sha256/cavp && sha256sum -c SHA256SUMS) && '
                              '(cd tests/transaction/sighash && sha256sum -c SHA256SUMS) && '
                              '(cd tests/transaction/corpus && sha256sum -c SHA256SUMS) && '
                              '(cd tests/work/mainnet-genesis-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/work/mainnet-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-auxpow-activation-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-600000-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-bip65-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-bip66-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-auxpow-activation-full-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-bip65-full-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-bip66-full-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-subsidy-prev-hashes && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-blocks/ranges/A && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-blocks/ranges/B && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-blocks/ranges/C && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-blocks/ranges/D && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-blocks/ranges/E1 && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-blocks/ranges/E2 && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-blocks/ranges/F && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-blocks/ranges/H && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-blocks/rule-changes && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-blocks/version-bits-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/regtest-header-sequences && sha256sum -c SHA256SUMS) && '
                              '(cd tests/proposals/impact/runs && sha256sum -c SHA256SUMS) && '
                              '(cd tests/script/campaign && sha256sum -c SHA256SUMS) && '
                              '(cd tests/script/corpus && sha256sum -c SHA256SUMS) && '
                              '(cd tests/script/signed-spends && sha256sum -c SHA256SUMS)',
            'refinement': 'lake -d Refinement build --wfail',
            'soundness-review': None,
            'writing': 'uv run --no-project --python 3.12 python scripts/check_writing.py --base main',
            'oracle': 'bash scripts/test_oracle.sh',
            'proposal-oracle': 'lake build dogelib-oracle dogelib-proposal-oracle proposal-test-oracle && '
                               'python3 -I scripts/test_proposal_oracle.py .lake/build/bin/dogelib-oracle .lake/build/bin/dogelib-proposal-oracle '
                               '.lake/build/bin/proposal-test-oracle',
            'core-comparison': 'scripts/build_core_harness.sh --trap-overflow <dogecoin-git-clone> build/core-harness && '
                               'python3 -I scripts/compare_core.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'rust-compactsize-comparison': 'cargo +nightly-2026-09-17 build --locked --manifest-path Refinement/Rust/Cargo.toml --example compactsize_oracle --jobs 4 && '
                                           'scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness && '
                                           'python3 -I scripts/compare_core.py --rust-compactsize Refinement/Rust/target/debug/examples/compactsize_oracle .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'signed-spend-regeneration': 'python3 -I scripts/check_signed_spends.py build/core-harness/core-signer',
            'campaign-self-test': 'python3 -I scripts/test_campaign.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'campaign-existing-requests': 'python3 -I scripts/campaign.py run --seed 20261108 --cases 10000 --seconds 600 --output build/campaign/check .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'campaign-generated-requests': 'python3 -I scripts/campaign.py run --campaign generated --signer build/core-harness/core-signer --seed 20261108 --cases 3000 --seconds 600 --batch-size 64 --output build/campaign/generated .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'campaign-proposal-search': 'python3 -I scripts/campaign.py run --campaign proposal --variant corrected --seed 0 --cases 374480 --output build/campaign/proposal .lake/build/bin/dogelib-oracle .lake/build/bin/proposal-replay',
            'campaign-regtest-replay': 'python3 -I scripts/test_campaign_production.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle --node build/core-node',
            'subsidy-seeds': 'python3 -I scripts/compare_subsidy_seeds.py --jobs 8 --output build/subsidy-seeds .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'subsidy-seeds-self-test': 'python3 -I scripts/test_compare_subsidy_seeds.py .lake/build/bin/dogelib-oracle',
            'version-bits-header-fixture': 'python3 -I scripts/fetch_version_bits_headers.py --check',
            'version-bits-walk': 'python3 -I scripts/compare_version_bits_walk.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'version-bits-walk-self-test': 'python3 -I scripts/compare_version_bits_walk.py --self-test .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'core-harness-state': 'python3 -I scripts/test_core_harness.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'csv-forced-active': 'python3 -I scripts/compare_csv_forced.py .lake/build/bin/dogelib-oracle .lake/build/bin/dogelib-proposal-oracle build/core-harness/core-oracle',
            'cutoff-candidates': 'python3 -I scripts/relative_lock_time_candidates.py --check',
            'impact-tools-self-test': 'python3 -I scripts/test_impact.py .lake/build/bin/proposal-test-oracle',
            'impact-run-to-10-000': 'python3 -I scripts/impact_run.py request --range genesis-10000 --fixture build/mainnet-blocks/genesis-10000 --output build/impact/requests/genesis-10000 && python3 -I scripts/impact_candidates.py --range genesis-10000 --request build/impact/requests/genesis-10000/request.json --check && python3 -I scripts/impact_run.py run --range genesis-10000 --request build/impact/requests/genesis-10000/request.json --revision RelativeLockTime --activation 1 --output build/impact/runs/genesis-10000 .lake/build/bin/dogelib-proposal-oracle',
            'impact-runs-short-range': 'python3 -I scripts/impact_run.py request --range short --fixture build/mainnet-blocks/genesis-10000 --harness build/core-harness/core-oracle --output build/impact/requests/short && python3 -I scripts/impact_candidates.py --range short --request build/impact/requests/short/request.json --check && python3 -I scripts/impact_run.py run --range short --request build/impact/requests/short/request.json --revision ExampleVersionVerify --activation none --output build/impact/runs/short/vv-none .lake/build/bin/proposal-test-oracle && python3 -I scripts/impact_run.py run --range short --request build/impact/requests/short/request.json --revision ExampleVersionVerify --activation 0 --output build/impact/runs/short/vv-0 .lake/build/bin/proposal-test-oracle && python3 -I scripts/impact_run.py run --range short --request build/impact/requests/short/request.json --revision ExampleFaultyLocktime/corrected --activation none --output build/impact/runs/short/fl-none .lake/build/bin/proposal-test-oracle && python3 -I scripts/impact_run.py run --range short --request build/impact/requests/short/request.json --revision ExampleFaultyLocktime/corrected --activation 0 --output build/impact/runs/short/fl-0 .lake/build/bin/proposal-test-oracle',
            'impact-runs-on-the-ranges': 'python3 -I scripts/impact_run.py run --range A --request build/impact/requests/A/request.json --revision RelativeLockTime --activation 1 --baseline build/range-runs/A/range-oracle-response.json --output build/impact/runs/A/RelativeLockTime-1 .lake/build/bin/dogelib-proposal-oracle',
            'impact-run-records': 'python3 -I scripts/impact_records.py --check && python3 -I scripts/impact_records.py --self-test',
            'impact-run-to-145-000': 'python3 -I scripts/impact_run.py run --range genesis-145000 --request build/impact/requests/genesis-145000/request.json --revision RelativeLockTime --activation 1 --output build/impact/runs/genesis-145000 .lake/build/bin/dogelib-proposal-oracle',
            'comparator-self-test': 'python3 -I scripts/test_compare_core.py .lake/build/bin/dogelib-oracle',
            'writing-checker-tests': 'uv run --no-project --python 3.12 python -m unittest scripts/test_check_writing.py',
            'script-corpus-freshness': 'python3 -I scripts/convert_script_tests.py --check',
            'script-corpus-converter-tests': 'python3 -I scripts/test_convert_script_tests.py',
            'full-header-fixture-check': 'python3 -I scripts/check_full_headers.py',
            'header-sequence-regeneration': 'python3 -I scripts/generate_header_sequences.py --check',
            'validation-report-tests': 'python3 -I scripts/test_validation_report.py',
            'block-fetch-tool-tests': 'python3 -I scripts/test_fetch_blocks.py',
            'block-count-tool-tests': 'python3 -I scripts/test_count_blocks.py',
            'rule-change-block-fixture': 'python3 -I scripts/fetch_blocks.py --check tests/block/mainnet-blocks/rule-changes',
            'release-block-fetch-tests': 'python3 -I scripts/test_fetch_release_blocks.py',
            'mainnet-block-ranges': 'python3 -I scripts/fetch_release_blocks.py && '
                                    'python3 -I scripts/compare_core.py --mainnet-blocks build/mainnet-blocks .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'mainnet-replay-to-145-000': 'python3 -I scripts/replay_blocks.py --last 145000 --output build/replay-145000 .lake/build/bin/dogelib-oracle build/core-harness/core-oracle '
                                         'build/mainnet-blocks/genesis-10000 build/mainnet-blocks/range-10001-145000',
            'replay-tool-self-test': 'python3 -I scripts/test_replay_blocks.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'snapshot-range-short-form': 'python3 -I scripts/snapshot_range.py --start 9000 --end 10000 --output build/snapshot-range/short '
                                         '.lake/build/bin/dogelib-oracle build/core-harness/core-oracle build/mainnet-blocks/genesis-10000',
            'snapshot-range-s': 'python3 -I scripts/snapshot_range.py --start 100000 --end 101000 --snapshot 145000 --jobs 3 --output build/snapshot-range/s '
                                '.lake/build/bin/dogelib-oracle build/core-harness/core-oracle '
                                'build/mainnet-blocks/genesis-10000 build/mainnet-blocks/range-10001-145000',
            'core-pass-self-test': 'python3 -I scripts/test_core_pass.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle '
                                   'build/core-harness/core-oracle-trap build/mainnet-blocks/genesis-10000',
            'core-pass': 'python3 -I scripts/core_pass.py --state build/core-pass --local build/mainnet-blocks/genesis-10000 '
                         '--local build/mainnet-blocks/range-10001-145000 build/core-harness/core-oracle-trap',
            'mainnet-range': 'python3 -I scripts/run_range.py --range A --pass build/core-pass --fixture build/ranges/A '
                             '--output build/range-runs/A .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'lane-tool': 'bash scripts/test_lane.sh',
        }
        self.assertEqual({g['slug']: g['command'] for g in gates}, expected)
        for gate in gates:
            if gate['command']:
                # Each placeholder, such as <dogecoin-git-clone>, stands for one path.
                result = subprocess.run(['bash', '-n', '-c', re.sub(r'<[^<>]+>', 'path', gate['command'])])
                self.assertEqual(result.returncode, 0, gate['name'])


if __name__ == '__main__':
    unittest.main()
