#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
python3 -m pip install --quiet sympy
python3 q6154/symbolic2.py | tee q6154/symbolic2.txt
sudo apt-get update -qq
sudo apt-get install -y singular >/dev/null
cat > q6154/factor.sing <<'EOF'
ring r=2,(u,v),dp;
poly R=v4+u3*v3+(u+u3)*v2+(u3+u4)*v+u7;
factorize(R);
EOF
Singular -q q6154/factor.sing | tee q6154/factor-mod2.txt
