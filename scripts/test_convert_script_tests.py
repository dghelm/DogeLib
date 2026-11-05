#!/usr/bin/env python3
"""Check corpus conversion against hand-derived bytes and pinned records."""

import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('converter', ROOT / 'scripts/convert_script_tests.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)


class Assembly(unittest.TestCase):
    def test_syntax_forms(self):
        cases = {
            '': '', ' \t\n ': '', '-1 0 1 16': '4f005160',
            '17 -17 127 128 -128 255 256': '01110191017f02800002808002ff00020001',
            '2147483647 -2147483647': '04ffffff7f04ffffffff',
            '9223372036854775807': '08ffffffffffffff7f',
            "'Az' '' '1'": '02417a000131',
            '0x4c 0x02 0xabac': '4c02abac',
            'DUP OP_DUP RESERVED OP_RESERVED': '76765050',
            'CHECKLOCKTIMEVERIFY OP_CHECKSEQUENCEVERIFY': 'b1b2',
            '- -0 0001': '000051',
        }
        for assembly, expected in cases.items():
            with self.subTest(assembly=assembly):
                self.assertEqual(c.assemble(assembly).hex(), expected)
        for n in range(1, 17):
            self.assertEqual(c.assemble(str(n)), bytes([0x50 + n]))

    def test_push_boundaries(self):
        for n, prefix in ((75, '4b'), (76, '4c4c'), (255, '4cff'),
                          (256, '4d0001'), (65535, '4dffff'), (65536, '4e00000100')):
            self.assertEqual(c.assemble("'" + 'a' * n + "'"), bytes.fromhex(prefix) + b'a' * n)

    def test_rejected_syntax(self):
        for text in ('OP_1', 'OP_0', 'NOP2', 'OP_NOP3', 'PUSHDATA1',
                     'OP_INVALIDOPCODE', '0x', '0x1', '0xgg', "'two words'", '1\r2'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                c.assemble(text)
        with self.assertRaisesRegex(ValueError, 'undefined'):
            c.assemble('-9223372036854775808')

    def test_opcode_table(self):
        # Independent landmarks from script.h and GetOpName, including gaps.
        for name, value in {'NOP': 0x61, 'TUCK': 0x7d, 'SIZE': 0x82,
                            '1ADD': 0x8b, 'WITHIN': 0xa5, 'SHA256': 0xa8,
                            'CHECKMULTISIGVERIFY': 0xaf, 'NOP10': 0xb9}.items():
            self.assertEqual(c.assemble(name + ' OP_' + name), bytes([value, value]))


class Records(unittest.TestCase):
    def row(self, sig='', pub='1', flags='', error='OK', witness=None):
        row = [sig, pub, flags, error, 'comment']
        return c.convert(json.dumps([([witness] + row) if witness is not None else row]))[0]

    def test_source_locations_and_comments(self):
        rows = c.convert('[\n["heading"],\n["",\n"1", "NONE", "OK", "detail"]\n]')
        self.assertEqual(len(rows), 1)
        self.assertEqual((rows[0]['source_index'], rows[0]['source_line'], rows[0]['comment']), (1, 3, 'detail'))
        self.assertEqual(rows[0]['flags'], [])

    def test_flags_and_witness(self):
        r = self.row(flags='CLEANSTACK')
        self.assertEqual(r['flags'], ['CLEANSTACK'])
        self.assertEqual(r['effective_flags'], ['CLEANSTACK', 'P2SH', 'WITNESS'])
        self.assertEqual(r['classification']['milestone'], 'outside')
        self.assertEqual(self.row(witness=[0])['classification']['milestone'], 'inside')
        self.assertEqual(self.row(witness=['', 0])['classification']['reasons'], ['nonempty_witness'])
        r = self.row(witness=['aa', 0.00000001])
        self.assertEqual(r['context']['amount_satoshis'], 1)
        self.assertEqual(r['witness'], ['aa'])
        with self.assertRaises(KeyError):
            self.row(flags='P2SH, TYPO')
        with self.assertRaises(ValueError):
            self.row(error='TYPO')

    def test_stage_estimates_ignore_push_payloads(self):
        for sig, pub, flags, stage in (
                ('0x01ac', '1', '', 2), ('0x4c01ae', '1', '', 2),
                ('0x4d0100ac', '1', '', 2), ('0x4e01000000af', '1', '', 2),
                ('CHECKSIG', '1', '', 3), ('', 'CHECKMULTISIG', '', 3),
                ('', 'CHECKSEQUENCEVERIFY', '', 2),
                ('', 'CHECKSEQUENCEVERIFY', 'CHECKSEQUENCEVERIFY', 4),
                ('', 'CHECKLOCKTIMEVERIFY', 'CHECKLOCKTIMEVERIFY', 4),
                ('', '0xa914' + '11' * 20 + '87', 'P2SH', 4),
                ('', '0xa914' + '11' * 20 + '87', '', 2),
                ('0x4c', '1', '', 2)):
            with self.subTest(sig=sig, pub=pub, flags=flags):
                self.assertEqual(self.row(sig, pub, flags)['classification']['estimated_stage'], stage)

    def test_malformed_records(self):
        for text in ('[] junk', '[[],]', '[{}]', '[1]', '[[]]', '{}', '[0]'):
            with self.subTest(text=text), self.assertRaises((ValueError, TypeError)):
                c.convert(text)
        with self.assertRaisesRegex(ValueError, 'portable'):
            c.context(b'', b'', 1 << 31)

    def test_context_bytes(self):
        r = self.row()
        # Version 1, one coinbase input, script 0000, final sequence,
        # one zero-valued OP_1 output, and zero locktime.
        credit = ('0100000001' + '00' * 32 + 'ffffffff020000ffffffff01' +
                  '00' * 8 + '0151' + '00000000')
        self.assertEqual(r['context']['crediting_tx_base_hex'], credit)
        spend = bytes.fromhex(r['context']['spending_tx_base_hex'])
        self.assertEqual(spend[:5].hex(), '0100000001')
        self.assertEqual(spend[37:].hex(), '0000000000ffffffff01' + '00' * 8 + '0000000000')

    def test_pinned_totals_and_rerun(self):
        records = c.convert((c.CORPUS / 'script_tests.json').read_text())
        self.assertEqual(len(records), 1193)
        for name, expected in c.outputs().items():
            self.assertEqual((c.CORPUS / name).read_bytes(), expected)
        result = subprocess.run(['python3', '-I', str(ROOT / 'scripts/convert_script_tests.py'), '--check'], capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_check_rejects_stale_output_without_writes(self):
        original = c.CORPUS
        # AGENTS.md requires lane scratch files under .lane/.
        (ROOT / '.lane').mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=ROOT / '.lane') as directory:
            c.CORPUS = Path(directory)
            try:
                (c.CORPUS / 'script_tests.json').write_bytes((original / 'script_tests.json').read_bytes())
                self.assertFalse((c.CORPUS / 'summary.json').exists())
                # Exercise CLI main with a stale file and a missing file.
                (c.CORPUS / 'script_tests.jsonl').write_bytes(b'stale\n')
                import sys
                old = sys.argv
                sys.argv = ['converter', '--check']
                try:
                    with self.assertRaises(SystemExit) as error:
                        c.main()
                    self.assertEqual(error.exception.code, 1)
                finally:
                    sys.argv = old
                self.assertEqual((c.CORPUS / 'script_tests.jsonl').read_bytes(), b'stale\n')
                self.assertFalse((c.CORPUS / 'summary.json').exists())
            finally:
                c.CORPUS = original


if __name__ == '__main__':
    unittest.main()
