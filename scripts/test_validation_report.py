#!/usr/bin/env python3
"""Check report evidence, gate execution and the repository's registry."""

import importlib.util
import os
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
        self.assertGreaterEqual(len(gates), 15)
        self.assertIn('validation-report-tests', {g['slug'] for g in gates})
        for gate in gates:
            if gate['command']:
                result = subprocess.run(['bash', '-n', '-c', gate['command'].replace('<dogecoin-git-clone>', 'core')])
                self.assertEqual(result.returncode, 0, gate['name'])


if __name__ == '__main__':
    unittest.main()
