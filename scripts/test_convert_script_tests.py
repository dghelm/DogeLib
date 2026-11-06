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
                for name in ('script_tests.json', 'tx_valid.json', 'tx_invalid.json'):
                    (c.CORPUS / name).write_bytes((original / name).read_bytes())
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


class TransactionRecords(unittest.TestCase):
    # Hand-built version 1 transactions use one-byte counts and script lengths.
    A = '000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f'
    B = '22' * 32

    def tx(self, inputs=None, outputs=None, witness=None, trailing=''):
        if inputs is None:
            inputs = [(self.A, 0, '')]
        if outputs is None:
            outputs = [(0, '51')]
        body = bytes([len(inputs)])
        for txid, n, sig in inputs:
            script = bytes.fromhex(sig)
            body += (bytes.fromhex(txid)[::-1] + n.to_bytes(4, 'little') +
                     bytes([len(script)]) + script + b'\xff' * 4)
        body += bytes([len(outputs)])
        for amount, pub in outputs:
            script = bytes.fromhex(pub)
            body += amount.to_bytes(8, 'little', signed=True) + bytes([len(script)]) + script
        if witness is not None:
            body = b'\x00\x01' + body
            for stack in witness:
                body += bytes([len(stack)])
                for item in stack:
                    data = bytes.fromhex(item)
                    body += bytes([len(data)]) + data
        return '01000000' + body.hex() + '00000000' + trailing

    def convert(self, tx=None, prevouts=None, flags='NONE', expectation='invalid'):
        row = [prevouts if prevouts is not None else [[self.A, 0, '1']],
               tx or self.tx(), flags]
        return c.convert_transactions(json.dumps([row]), 'tx_' + expectation + '.json', expectation)

    def test_all_flag_bits(self):
        # interpreter.h bit positions, independent of the converter table.
        names = ['P2SH', 'STRICTENC', 'DERSIG', 'LOW_S', 'NULLDUMMY',
                 'SIGPUSHONLY', 'MINIMALDATA', 'DISCOURAGE_UPGRADABLE_NOPS',
                 'CLEANSTACK', 'CHECKLOCKTIMEVERIFY', 'CHECKSEQUENCEVERIFY',
                 'WITNESS', 'DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM',
                 'MINIMALIF', 'NULLFAIL', 'WITNESS_PUBKEYTYPE']
        for bit, name in enumerate(names):
            self.assertEqual(c.parse_flags(name), 1 << bit)
        self.assertEqual(c.parse_flags('NONE'), 0)
        self.assertEqual(c.parse_flags(''), 0)
        self.assertEqual(c.parse_flags('NONE,P2SH,DERSIG,P2SH'), 5)
        for flags in ('TYPO', 'P2SH, STRICTENC', 'P2SH,', ','):
            with self.assertRaises(KeyError):
                c.parse_flags(flags)

    def test_multi_input_join_and_expectations(self):
        tx = self.tx([(self.B, 1, '52'), (self.A, 0, '51')])
        prevouts = [[self.A, 0, 'CHECKSIG'], [self.B, 1, '1', -7]]
        records, counts = self.convert(tx, prevouts, expectation='valid')
        self.assertEqual(counts['transactions'], 1)
        self.assertEqual(counts['inputs'], 2)
        self.assertEqual([r['input_index'] for r in records], [0, 1])
        self.assertEqual([r['prevout_txid'] for r in records], [self.B, self.A])
        self.assertEqual([r['prevout_scriptPubKey_hex'] for r in records], ['51', 'ac'])
        self.assertEqual([r['scriptSig_hex'] for r in records], ['52', '51'])
        self.assertEqual(records[0]['prevout_amount'], -7)
        self.assertNotIn('prevout_amount', records[1])
        for r in records:
            self.assertEqual(r['tx_hex'], tx)
            self.assertEqual(r['per_input_expectation'], 'accept')
            self.assertEqual(r['per_input_expectation_source'], c.RUNNER + ':155-176')
        rejected, _ = self.convert(tx, prevouts)
        self.assertTrue(all(r['per_input_expectation'] is None for r in rejected))
        self.assertTrue(all('no individual input outcome' in r['per_input_expectation_reason']
                            for r in rejected))

    def test_comments_and_source_locations(self):
        row = json.dumps([[[self.A, 0, '1']], self.tx(), 'NONE'])
        text = '[\n["first"],\n["second"],\n' + row + ',\n' + row + ',\n["next"],\n' + row + ']'
        records, _ = c.convert_transactions(text, 'tx_valid.json', 'valid')
        self.assertEqual([r['comment'] for r in records], [['first', 'second'], ['first', 'second'], ['next']])
        self.assertEqual([r['source_index'] for r in records], [2, 3, 5])
        self.assertEqual([r['source_line'] for r in records], [4, 5, 7])
        self.assertTrue(all(r['source_file'] == 'tx_valid.json' for r in records))
        self.assertEqual(self.convert()[0][0]['comment'], [])

    def test_witness_and_flags_exclusions(self):
        r = self.convert(self.tx(witness=[['']]))[0][0]
        self.assertEqual(r['witness'], [''])
        self.assertEqual(r['classification']['reasons'], ['nonempty_witness'])
        self.assertEqual(c.read_transaction(self.tx(witness=[['aa']]))['base_size'],
                         len(bytes.fromhex(self.tx())))
        self.assertEqual(self.convert(self.tx(witness=[[]]))[0][0]['classification']['milestone'], 'inside')
        for flag in c.FLAG_NAMES:
            r = self.convert(flags=flag)[0][0]
            reasons = r['classification']['reasons']
            self.assertEqual(reasons, [] if flag in c.APPROVED else ['flag:' + flag])
        # Transaction tests pass CLEANSTACK unchanged, unlike script_tests.
        self.assertEqual(self.convert(flags='CLEANSTACK')[0][0]['flags_mask'], 256)

    def test_stage_features(self):
        for pub, flags, stage in [('0x01ac', 'NONE', 2), ('CHECKSIG', 'NONE', 3),
                                  ('CHECKLOCKTIMEVERIFY', 'CHECKLOCKTIMEVERIFY', 4),
                                  ('HASH160 0x14 0x' + '33' * 20 + ' EQUAL', 'P2SH', 4)]:
            r = self.convert(prevouts=[[self.A, 0, pub]], flags=flags)[0][0]
            self.assertEqual(r['classification']['estimated_stage'], stage)

    def test_prevout_map_and_uint32_index(self):
        tx = self.tx([('00' * 32, 0xffffffff, '0000')])
        prevouts = [['00' * 32, -1, '0', 4], ['00' * 32, -1, '1']]
        r = self.convert(tx, prevouts)[0][0]
        self.assertEqual((r['prevout_n'], r['prevout_scriptPubKey_hex'], r['prevout_amount']),
                         (0xffffffff, '51', 4))
        with self.assertRaisesRegex(ValueError, 'missing prevout'):
            self.convert(prevouts=[])
        for prevout in ([self.A, 0, '1', 1 << 63], [self.A, 1 << 31, '1'], ['xyz', 0, '1']):
            with self.assertRaises(ValueError):
                self.convert(prevouts=[prevout])

    def test_prefix_and_malformed_transactions(self):
        parsed = c.read_transaction(self.tx(trailing='aabb'))
        self.assertEqual(parsed['trailing_bytes'], 2)
        self.assertEqual(parsed['base_size'], len(bytes.fromhex(self.tx())))
        self.assertEqual(self.convert(self.tx(trailing='AA'))[0][0]['tx_hex'], self.tx(trailing='AA'))
        tx = self.tx()
        for bad in (tx[:-2], tx + 'x', 'gg', tx[:8] + 'fd0100' + tx[10:],
                    tx[:8] + 'fe01000002' + tx[10:],
                    '010000000002' + tx[8:]):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                c.read_transaction(bad)
        empty = c.read_transaction('01000000000000000000')
        self.assertEqual(empty['inputs'], [])
        self.assertEqual(empty['outputs'], [])
        self.assertEqual(empty['base_size'], 10)
        records, summary = self.convert('01000000000000000000', [])
        self.assertEqual(records, [])
        self.assertEqual(summary['zero_input_transactions'], 1)
        # The pinned reader accepts an all-empty witness encoding.
        self.assertEqual(c.read_transaction(self.tx(witness=[[]]))['inputs'][0]['witness'], [])

    def test_check_transaction_order_and_boundaries(self):
        def reason(tx):
            result = c.estimate_check_transaction(c.read_transaction(tx))
            self.assertTrue(result['estimated'])
            self.assertEqual(result['rejects_before_script'], result['reason'] is not None)
            return result['reason']
        self.assertEqual(reason('01000000000000000000'), 'bad-txns-vin-empty')
        self.assertEqual(reason(self.tx(outputs=[])), 'bad-txns-vout-empty')
        for amount, expected in [(-1, 'bad-txns-vout-negative'), (10**18, None),
                                 (10**18 + 1, 'bad-txns-vout-toolarge')]:
            self.assertEqual(reason(self.tx(outputs=[(amount, '')])), expected)
        self.assertEqual(reason(self.tx(outputs=[(10**18, ''), (1, '')])), 'bad-txns-txouttotal-toolarge')
        duplicate = [(self.A, 0, ''), (self.A, 0, '')]
        self.assertEqual(reason(self.tx(duplicate)), 'bad-txns-inputs-duplicate')
        self.assertEqual(reason(self.tx(duplicate, [(-1, '')])), 'bad-txns-vout-negative')
        null = ('00' * 32, 0xffffffff)
        for length in (0, 1, 2, 100, 101):
            expected = None if 2 <= length <= 100 else 'bad-cb-length'
            self.assertEqual(reason(self.tx([(*null, '00' * length)])), expected)
        self.assertEqual(reason(self.tx([(*null, ''), (self.A, 0, '')])), 'bad-txns-prevout-null')
        tx = c.read_transaction(self.tx())
        for size, expected in [(1000000, None), (1000001, 'bad-txns-oversize')]:
            tx['base_size'] = size
            self.assertEqual(c.estimate_check_transaction(tx)['reason'], expected)

    def test_pinned_totals_and_invalid_boundaries(self):
        all_records = []
        for expectation, count, inputs in [('valid', 118, 171), ('invalid', 80, 96)]:
            name = f'tx_{expectation}.json'
            records, summary = c.convert_transactions((c.CORPUS / name).read_text(), name, expectation)
            self.assertEqual((summary['transactions'], summary['inputs']), (count, inputs))
            all_records.extend(records)
            if expectation == 'valid':
                self.assertTrue(all(not r['classification']['check_transaction']['rejects_before_script'] for r in records))
            else:
                self.assertTrue(all(r['per_input_expectation'] is None for r in records))
                self.assertTrue(any(r['classification']['check_transaction']['rejects_before_script'] for r in records))
                self.assertTrue(any(not r['classification']['check_transaction']['rejects_before_script'] for r in records))
        inside = sum(r['classification']['milestone'] == 'inside' for r in all_records)
        self.assertEqual((len(all_records), inside, len(all_records) - inside), (267, 159, 108))

    def test_transaction_freshness_rejects_missing_and_stale(self):
        import contextlib
        import io
        import sys
        original = c.CORPUS
        with tempfile.TemporaryDirectory(dir=ROOT / '.lane') as directory:
            try:
                c.CORPUS = Path(directory)
                for name in ('script_tests.json', 'tx_valid.json', 'tx_invalid.json'):
                    (c.CORPUS / name).write_bytes((original / name).read_bytes())
                generated = c.outputs()
                for name, data in generated.items():
                    (c.CORPUS / name).write_bytes(data)
                for target in ('tx_spends.jsonl', 'tx_spends.summary.json'):
                    for stale in (None, b'stale\n'):
                        path = c.CORPUS / target
                        if stale is None:
                            path.unlink()
                        else:
                            path.write_bytes(stale)
                        before = {p.name: p.read_bytes() for p in c.CORPUS.iterdir()}
                        old = sys.argv
                        sys.argv = ['converter', '--check']
                        try:
                            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                                c.main()
                        finally:
                            sys.argv = old
                        self.assertEqual(before, {p.name: p.read_bytes() for p in c.CORPUS.iterdir()})
                        path.write_bytes(generated[target])
            finally:
                c.CORPUS = original


if __name__ == '__main__':
    unittest.main()
