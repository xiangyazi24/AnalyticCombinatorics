# Task — Compositions OGF closed form

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

**Goal:** Prove the closed-form OGF identity for integer compositions:

```
compositionClass.ogfZ · (1 - 2 X) = 1 - X    (over ℤ[[z]])
```

This is the analogue of `permClass_egf_mul_one_sub_X` in the OGF world.

Combinatorial fact: `compositionClass.count 0 = 1` and `compositionClass.count (n+1) = 2^n`.
Generating function:
```
∑ count(n) z^n = 1 + ∑_{n≥1} 2^{n-1} z^n = 1 + z/(1-2z) = (1-z)/(1-2z)
```
i.e. `(1 - 2z) · compositionClass.ogfZ = 1 - z`.

## Required code

```lean
theorem compositionClass_ogfZ_mul_one_sub_two_X :
    ogfZ compositionClass * (1 - 2 * PowerSeries.X) = 1 - PowerSeries.X := by
  sorry
```

## Strategy hint

Coefficient comparison at `n`. Use:
- `compositionClass_count_zero` (count 0 = 1)
- `compositionClass_count_succ` (count (n+1) = 2^n)
- `PowerSeries.coeff_mul`, `coeff_X`, `coeff_one`, `coeff_X_mul`
- `ogfZ` / `coeff_ogf` for ours
- For `2 * X` you may need `coeff` of scalar multiples; `PowerSeries.smul` lemmas

The proof should split into n=0 and n=k+1 cases, use `Finset.sum_eq_single`
to pick out the only nonzero antidiag terms.

## Reply file

`HANDOFF/outbox/task-compositions-ogf-reply.md` — call Write tool to actually
create the file. Don't print to chat only. See "Phantom-write hazard" in HANDOFF.md.
