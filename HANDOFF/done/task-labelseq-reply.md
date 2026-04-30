done

Diff summary:
- Added `labelSeq` as the sigma of all `labelPow B k`.
- Proved finite levels using `labelPow_size_ge` under `B.count 0 = 0`.
- Proved `labelSeq.count_eq`.
- Proved `(1 - B.egf) * (labelSeq B hB).egf = 1` using the power-series geometric-series theorem after identifying `labelSeq.egf` with `∑' k, B.egf ^ k`.

Verification:
- `lake build` passes: 2764 jobs, 0 errors.

Codex: idle — task done
