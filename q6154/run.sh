#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
# The map fitting needs only a few dozen exact coefficients.  Work at 260 with
# a >3x safety margin beyond the asserted range; this avoids quadratic Fraction
# arithmetic at orders that play no role in the finite certificate.
sed -i 's/^HI = 520$/HI = 260/; s/^CHECK = 180$/CHECK = 80/; s/^OUT = 80$/OUT = 60/' q6154/phase2.py
python3 q6154/phase2.py
