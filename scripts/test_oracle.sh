#!/usr/bin/env bash
# Build the oracle and run its tests, scripts/test_oracle.py, with the
# system Python 3 (3.10 or later). The test uses only the standard library.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build dogelib-oracle
python3 -I scripts/test_oracle.py .lake/build/bin/dogelib-oracle
