#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
python3 q6154/make_delivery.py | tee q6154/delivery-build.log
