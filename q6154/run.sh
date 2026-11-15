#!/usr/bin/env bash
set -euo pipefail
mkdir -p q6154
python3 - <<'PY'
from pathlib import Path
p=Path('q6154/micro-report.md')
b=p.read_bytes()
assert b.endswith(b'\n')
Path('q6154/micro-report-noeol.md').write_bytes(b[:-1])
PY
