#!/usr/bin/env python3
from __future__ import annotations
import base64
import hashlib
import json
import lzma
from pathlib import Path

ROOT = Path('q6154')
report = (ROOT/'report.md').read_text()
data = json.loads((ROOT/'check-data.json').read_text())

# Fixed-length exact binary codec: for each of U,V, reset prev=0, delta-code,
# zigzag each signed delta, then unsigned LEB128.  Finally LZMA2 compress.
def put_varint(buf: bytearray, n: int) -> None:
    assert n >= 0
    while n >= 128:
        buf.append((n & 127) | 128)
        n >>= 7
    buf.append(n)

raw = bytearray()
for arr in (data['U'], data['V']):
    prev = 0
    for x in arr:
        d = x - prev
        prev = x
        z = 2*d if d >= 0 else -2*d-1
        put_varint(raw, z)
packed = lzma.compress(bytes(raw), format=lzma.FORMAT_XZ,
                       preset=9 | lzma.PRESET_EXTREME)
b64 = base64.b64encode(packed).decode()
wrapped = '\n'.join(b64[i:i+100] for i in range(0, len(b64), 100))

old_start = report.index('The following block is a zlib-compressed')
old_end_marker = 'Canonical CSV fingerprints of the decoded arrays are:'
old_end = report.index(old_end_marker, old_start)

replacement = f'''The following block is an exact binary encoding of the 10,002 coefficients.  For each fixed-length array (`U` first, then `V`, 5,001 entries each), it resets the previous value to zero, delta-codes, zigzag-encodes each signed delta, writes unsigned LEB128, then applies XZ/LZMA2.  The block is base64.  This is the complete exact integer data, not a sample.  Decode with the stdlib snippet immediately below it.

```text
{wrapped}
```

```python
import base64, lzma
blob = """PASTE_THE_BLOCK_ABOVE""".replace("\\n", "")
b = lzma.decompress(base64.b64decode(blob))
pos = 0

def get_varint():
    global pos
    z = shift = 0
    while True:
        c = b[pos]; pos += 1
        z |= (c & 127) << shift
        if c < 128:
            return z
        shift += 7

arrays = []
for _ in range(2):
    arr, prev = [], 0
    for _ in range(5001):
        z = get_varint()
        d = (z >> 1) ^ -(z & 1)
        prev += d
        arr.append(prev)
    arrays.append(arr)
U, V = arrays
assert pos == len(b)
```

Packed-byte SHA-256: `{hashlib.sha256(packed).hexdigest()}`.

'''
compact = report[:old_start] + replacement + report[old_end:]
(ROOT/'report-compact.md').write_text(compact)
print('raw varint bytes', len(raw))
print('packed bytes', len(packed))
print('base64 chars', len(b64))
print('compact report bytes', len(compact.encode()))
print('compact report lines', compact.count('\n'))
print('compact report sha256', hashlib.sha256(compact.encode()).hexdigest())
print('first', compact.splitlines()[0])
print('last', compact.splitlines()[-1])
