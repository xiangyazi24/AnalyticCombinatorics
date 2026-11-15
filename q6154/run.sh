#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
cp q6154/phase2.py q6154/phase2_diag.py
sed -i 's/^HI = 520$/HI = 260/; s/^HI = 260$/HI = 260/; s/^CHECK = 180$/CHECK = 100/; s/^CHECK = 80$/CHECK = 100/; s/^OUT = 80$/OUT = 100/; s/^OUT = 60$/OUT = 100/' q6154/phase2_diag.py
python3 - <<'PY'
p='q6154/phase2_diag.py'
s=open(p).read()
a=s.index('    Q = ',s.index('def main():'))
b=s.index('    Q.assert_zero',a)
new='''    Q = -x*z - x*w + y**2 + y*z + z*w
    C = (x**2*w + x*y*z - x*y*w - x*z*w +
         y*z*w + z**2*w - z*w**2)
'''
open(p,'w').write(s[:a]+new+s[b:])
PY
python3 q6154/phase2_diag.py
