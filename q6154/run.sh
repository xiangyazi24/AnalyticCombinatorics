#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
python3 q6154/compact_report.py | tee q6154/compact-build.log
