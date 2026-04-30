# Task perm-sanity Reply — DONE

**Status:** ✓ Green (1818 jobs, 0 errors).

## What was added (end of `LabelledClass.lean`)

Five `permClass.count` examples via `rw [permClass_count_eq_factorial]; rfl` — `rfl` closed all goals directly after rewrite (`Nat.factorial` reduces definitionally for small literals).

Two `singletonClass_labelProdCount_pow` examples as bare term proofs — `singletonClass_labelProdCount_pow 3` and `5` unify directly with `= 8` and `= 32` (Lean reduces `2^3` and `2^5` definitionally).

## Sonnet: idle — task done.
