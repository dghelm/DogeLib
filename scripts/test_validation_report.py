#!/usr/bin/env python3
"""Check report evidence, gate execution and the repository's registry."""

import importlib.util
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


class WorkflowDependencies(unittest.TestCase):
    def test_core_packages_match_validation(self):
        packages = {}
        for workflow in ('core', 'validation'):
            text = (ROOT / f'.github/workflows/{workflow}.yml').read_text()
            installs = [shlex.split(line.strip()) for line in text.splitlines()
                        if line.strip().startswith('sudo apt-get install ')]
            self.assertEqual(len(installs), 1, workflow)
            packages[workflow] = {word for word in installs[0][3:] if not word.startswith('-')}
            self.assertIn('libboost-dev', packages[workflow], workflow)
        self.assertEqual(packages['core'], packages['validation'])


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
            'import-boundaries': 'lake env lean --run scripts/CheckRefinementImports.lean',
            'import-boundary-self-test': 'bash scripts/test_import_boundaries.sh',
            'rust-known-answers': 'cargo +nightly-2026-09-17 test --locked --manifest-path Refinement/Rust/Cargo.toml --jobs 4',
            'rust-extraction-freshness': 'Refinement/Rust/regenerate.sh --check',
            'declaration-check-self-test': 'bash scripts/test_check_decls.sh',
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
                              '(cd tests/block/mainnet-bip65-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-bip66-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-auxpow-activation-full-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-bip65-full-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/mainnet-bip66-full-headers && sha256sum -c SHA256SUMS) && '
                              '(cd tests/block/regtest-header-sequences && sha256sum -c SHA256SUMS) && '
                              '(cd tests/script/corpus && sha256sum -c SHA256SUMS) && '
                              '(cd tests/script/signed-spends && sha256sum -c SHA256SUMS)',
            'refinement': 'lake -d Refinement build --wfail',
            'soundness-review': None,
            'writing': 'uv run --no-project --python 3.12 python scripts/check_writing.py --base main',
            'oracle': 'bash scripts/test_oracle.sh',
            'core-comparison': 'scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness && '
                               'python3 -I scripts/compare_core.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'rust-compactsize-comparison': 'cargo +nightly-2026-09-17 build --locked --manifest-path Refinement/Rust/Cargo.toml --example compactsize_oracle --jobs 4 && '
                                           'scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness && '
                                           'python3 -I scripts/compare_core.py --rust-compactsize Refinement/Rust/target/debug/examples/compactsize_oracle .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'signed-spend-regeneration': 'python3 -I scripts/check_signed_spends.py build/core-harness/core-signer',
            'campaign-self-test': 'python3 -I scripts/test_campaign.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'campaign-existing-requests': 'python3 -I scripts/campaign.py run --seed 20261108 --cases 10000 --seconds 600 --output build/campaign/check .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'campaign-generated-requests': 'python3 -I scripts/campaign.py run --campaign generated --signer build/core-harness/core-signer --seed 20261108 --cases 3000 --seconds 600 --batch-size 64 --output build/campaign/generated .lake/build/bin/dogelib-oracle build/core-harness/core-oracle',
            'campaign-proposal-search': 'python3 -I scripts/campaign.py run --campaign proposal --variant corrected --seed 0 --cases 374480 --output build/campaign/proposal .lake/build/bin/dogelib-oracle .lake/build/bin/proposal-replay',
            'campaign-regtest-replay': 'python3 -I scripts/test_campaign_production.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle --node <node-build-dir>',
            'comparator-self-test': 'python3 -I scripts/test_compare_core.py .lake/build/bin/dogelib-oracle',
            'writing-checker-tests': 'uv run --no-project --python 3.12 python -m unittest scripts/test_check_writing.py',
            'script-corpus-freshness': 'python3 -I scripts/convert_script_tests.py --check',
            'script-corpus-converter-tests': 'python3 -I scripts/test_convert_script_tests.py',
            'full-header-fixture-check': 'python3 -I scripts/check_full_headers.py',
            'header-sequence-regeneration': 'python3 -I scripts/generate_header_sequences.py --check',
            'validation-report-tests': 'python3 -I scripts/test_validation_report.py',
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
