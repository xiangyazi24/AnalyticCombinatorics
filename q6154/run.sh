#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
python3 q6154/make_micro.py | tee q6154/micro-build.log
