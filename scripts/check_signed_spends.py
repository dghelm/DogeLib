"""Compare the committed signed-spend fixtures with a fresh Core-only run."""

import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
FIXTURE = ROOT / 'tests/script/signed-spends/recovery.jsonl'


def main():
    if len(sys.argv) != 2:
        print('usage: check_signed_spends.py <core-signer>', file=sys.stderr)
        return 2
    result = subprocess.run([sys.argv[1]], stdout=subprocess.PIPE, check=True, timeout=60)
    if result.stdout != FIXTURE.read_bytes():
        print('signed-spend fixtures differ from Core regeneration', file=sys.stderr)
        return 1
    print(f'signed-spend regeneration: {len(result.stdout.splitlines())} records match byte for byte')
    vectors = subprocess.run([sys.argv[1], '--verification-vectors'], stdout=subprocess.PIPE, check=True, timeout=60)
    if vectors.stdout != (ROOT / 'tests/cryptography/secp256k1/core/requests.jsonl').read_bytes():
        print('public-key requests differ from Core regeneration', file=sys.stderr)
        return 1
    print('public-key regeneration: 4 records match byte for byte')
    return 0


if __name__ == '__main__':
    sys.exit(main())
