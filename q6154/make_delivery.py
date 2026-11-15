#!/usr/bin/env python3
from pathlib import Path
import hashlib

ROOT = Path('q6154')
report = (ROOT/'report.md').read_text()
start = report.index('The following block is a zlib-compressed')
end_marker = 'Canonical CSV fingerprints of the decoded arrays are:'
end = report.index(end_marker, start)
replacement = '''The complete exact coefficient archive is pinned at source commit
`6ec28d99a2fd5915c2622d979220131a8e845582`, path `q6154/qexp.b85`
(blob SHA `71476bb782548700ddb7a46217f61ac62f63f481`).  It is the base85
encoding of a zlib-compressed UTF-8 JSON object
`{"U":[u_0,...,u_5000],"V":[v_0,...,v_5000]}`.  This archive is an
auxiliary copy of the data; the checker below independently recomputes every
coefficient from the defining Euler products and, with
`--dump qexp.json`, writes the same complete exact arrays.  Thus the markdown
remains self-contained even without the auxiliary archive.

Pinned raw archive:

```text
https://raw.githubusercontent.com/xiangyazi24/AnalyticCombinatorics/6ec28d99a2fd5915c2622d979220131a8e845582/q6154/qexp.b85
```

Stdlib decoder for the pinned archive:

```python
import base64, json, zlib
from pathlib import Path
blob = "".join(Path("qexp.b85").read_text().split())
qexp = json.loads(zlib.decompress(base64.b85decode(blob)))
U, V = qexp["U"], qexp["V"]
assert len(U) == len(V) == 5001
```

'''
delivery = report[:start] + replacement + report[end:]
out = ROOT/'delivery-report.md'
out.write_text(delivery)
print('bytes', len(delivery.encode()))
print('lines', delivery.count('\n'))
print('sha256', hashlib.sha256(delivery.encode()).hexdigest())
print('first', delivery.splitlines()[0])
print('last', delivery.splitlines()[-1])
