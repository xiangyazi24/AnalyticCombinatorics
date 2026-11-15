#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
python3 -m pip install --quiet sympy
cp q6154/phase2.py q6154/phase2_diag.py
sed -i 's/^HI = 520$/HI = 260/; s/^CHECK = 180$/CHECK = 100/; s/^OUT = 80$/OUT = 100/' q6154/phase2_diag.py
python3 q6154/fit_forward.py
