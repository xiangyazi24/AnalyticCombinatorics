# Task — exp coefficient identity at higher powers

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append)

**Goal:** Generalize `coeff_exp_sq_eq_pow_div_factorial` to higher powers.

```lean
/-- [zⁿ] (exp z)^k = k^n / n!. Generalizes coeff_exp_sq (k = 2). -/
theorem coeff_exp_pow_eq_pow_div_factorial (k n : ℕ) :
    coeff n ((PowerSeries.exp ℚ) ^ k) = (k ^ n : ℚ) / n.factorial := by
  -- Strategy: connect k-fold product of singletonClass via labelPow + labelPow_egf,
  -- then count = k^n via labelPow_count over singletonClass.
  -- But labelPow_egf is over A.egf^k for a class A. Since singletonClass.egf = exp:
  --   coeff n (exp^k) = coeff n (singletonClass.egf^k)
  --                   = (labelPow singletonClass k).count n / n!
  -- Need (labelPow singletonClass k).count n = k^n.
  sorry  -- if you can land it cleanly via labelPow + induction, great
         -- otherwise file blocker
```

## Strategy

```
coeff n ((exp ℚ) ^ k) 
  = coeff n (singletonClass.egf ^ k)   (by singletonClass_egf_eq_exp)
  = coeff n ((labelPow singletonClass k).egf)  (by labelPow_egf, reversed)
  = (labelPow singletonClass k).count n / n!  (by coeff_egf)
```

So need: `(labelPow singletonClass k).count n = k^n`. By induction on k:
- k = 0: labelPow singleton 0 = Epsilon, count n = δ_{n,0}, while k^n = 0^n = δ_{n,0}. Match.
- k+1: labelPow singleton (k+1) = singleton.labelProd (labelPow singleton k). 
  count n = ∑ p ∈ antidiag n, n.choose p.1 · 1 · (k^p.2)
         = ∑ p ∈ antidiag n, n.choose p.1 · k^p.2
         = (1+k)^n by binomial theorem.
  Done.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker with details)
- Reply at HANDOFF/outbox/task-egf-three-times-X-reply.md
