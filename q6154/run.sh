#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
cp q6154/phase2.py q6154/phase2-diag.py
sed -i 's/^HI = 520$/HI = 220/; s/^HI = 260$/HI = 220/; s/^CHECK = 180$/CHECK = 60/; s/^CHECK = 80$/CHECK = 60/; s/^OUT = 80$/OUT = 50/; s/^OUT = 60$/OUT = 50/' q6154/phase2-diag.py
sed -i 's/Q.assert_zero(0, CHECK, "canonical quadric")/print("Q_RESIDUAL", Q.val(), Q.lead())/; s/C.assert_zero(0, CHECK, "canonical cubic")/print("C_RESIDUAL", C.val(), C.lead())/' q6154/phase2-diag.py
python3 q6154/phase2-diag.py
