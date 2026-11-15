#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
python3 q6154/checker.py --dump q6154/check-data.json --emit-b85 q6154/qexp.b85 | tee q6154/checker.log
