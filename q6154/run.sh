#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
python3 -m pip install --quiet sympy
python3 q6154/symbolic_checks.py | tee q6154/symbolic-checks.txt
