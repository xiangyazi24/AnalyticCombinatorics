#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
python3 -m pip install --quiet sympy
python3 q6154/derive_inverse.py | tee q6154/inverse.txt
