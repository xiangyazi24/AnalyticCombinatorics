#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
cp q6154/phase2.py q6154/phase2_diag.py
sed -i 's/^HI = 520$/HI = 100/; s/^HI = 260$/HI = 100/; s/^CHECK = 180$/CHECK = 30/; s/^CHECK = 80$/CHECK = 30/; s/^OUT = 80$/OUT = 30/; s/^OUT = 60$/OUT = 30/' q6154/phase2_diag.py
python3 q6154/check_suth_fast.py
