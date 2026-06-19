# Quantitative singularity-analysis + saddle-point campaign — remaining checklist

Watch these clear one-by-one. Legend: [ ] open · [◐] in progress · [x] done (commit) · [⊘] skip.

## Already done (committed, clean-3) — reference
general-α 2nd-order transfer; √-family 2nd-order (Motzkin/Catalan/Schröder/Riordan/ternary/Cayley);
√-family 3rd-order (Motzkin/Catalan/Schröder/Riordan/ternary); 2nd & 3rd-order √-meta-applicators;
3rd-order model expansion; abstract 2nd-order saddle theorem; saddle instances involutions/Bell/Blocks3.
(~21 theorems, 11 commits.)

## REMAINING
- [x] T1. Cayley THIRD-order count. DONE. (Cayley has 2nd-order via Stirling; extend to 3rd.) FEASIBLE.
- [x] T2. Fragmented-perm finite-radius SECOND-order. WIP: 1 sorry = the finite-radius 2nd-order tail
       estimate (ρ=1, saddle r→1⁻). HARD (the design flagged finite-radius as the hardest regime).
- [ ] T3. Fuss-Catalan-general UNCONDITIONAL. Discharge the two-term Puiseux of B=1+zB^p at the branch
       point — needs a ramified/Puiseux analytic-inverse theorem, currently ABSENT from Mathlib. HARD/gap.
- [ ] T4. THIRD-order saddle-point layer. Extend the abstract 2nd-order saddle theorem to 3rd order
       (next Hermite-moment term), + one instance. SUBSTANTIAL (optional).
- [⊘] Exp 2nd-order: SKIP — [zⁿ]e^z = 1/n! exact, no asymptotic content.

## Plan
Clear T1 first (feasible). Then T2 (finite-radius 2nd-order, attack the tail). T3 needs the ramified-inverse
(Mathlib-level; attempt or document as a true gap). T4 optional after T1-T3.

**T3 UPDATE (resume):** The Puiseux/ramified-inverse gap is BYPASSABLE. Fuss-Catalan coeffs have the exact Raney closed form `[z^n]B=(1/((p-1)n+1))*C(pn,n)`; Stirling on the factorial ratio (reusing CayleySecondOrder's `log(stirlingSeq n)-log(stirlingSeq(n+1))` squeeze) gives the asymptotics unconditionally — no analytic-inverse needed. Independently re-derived c1 = -(p^2+11p+1)/(12p(p-1)) (matches prior). Awaiting ChatGPT(ac) for c2 cross-check.

### T3 FULL SOLUTION (resume, verified vs ground truth)

Generalized Fuss-Catalan B(z)=1+z·B(z)^p, p≥2. Exact Raney coeff:
  [z^n]B = (1/((p-1)n+1))·C(pn,n) = (1/((p-1)n+1))·(pn)!/(n!·((p-1)n)!).
Write q=p-1, pq=p(p-1). Stirling on the 3-factorial ratio (n^n powers cancel
exactly → ρ^{-n} with ρ=q^q/p^p; sqrt-prefactor exact → n^{-3/2}; all 1/n,1/n^2
corrections come from exp(Stirling 1/(12m) series) × the 1/((p-1)n+1) denominator):

  c_S = -(1+pq)/(12 pq)
  c0  = sqrt(p/(2π q))/q                         [leading, ρ^{-n} n^{-3/2}]
  c1  = c_S - 1/q = -(p^2+11p+1)/(12 p (p-1))    [relative n^{-1}]
  c2  = 1/q^2 - c_S/q + c_S^2/2                   [relative n^{-2}]

GROUND-TRUTH CHECK p=2 (Catalan): c1=-9/8, c2=145/128 — matches the known
C_n = 4^n/(√π n^{3/2})(1 - 9/8 n^{-1} + 145/128 n^{-2} - ...) exactly.
p=3: c1=-43/72, c2=3145/10368.  p=4: c1=-61/144, c2=6025/41472.

CONCLUSION: the "ramified-Puiseux Mathlib gap" is ILLUSORY for this family.
Lean route = reuse CayleySecondOrder/CayleyThirdOrder Stirling-squeeze
(stirlingSeq, tail 1/(12n), lower 1/(12n)-1/n^3), applied to 3 args (pn,n,qn)
+ the 1/((p-1)n+1) prefactor. No analytic-inverse, unconditional.

### T4 SOLUTION (resume, derived + verified on 2 functions)

Third-order saddle-point (Hayman) correction, extending δ1 = b4/(8b²) - 5b3²/(24b³):

  δ2 = -b6/(48 b³) + (7/48) b3 b5/b⁴ + (35/384) b4²/b⁴
       - (35/64) b3² b4/b⁵ + (385/1152) b3⁴/b⁶

where b=b2,b3,b4,b5,b6 are the 2nd..6th θ-derivatives of the saddle phase.
Derived via Wick/cumulant expansion of ∫exp(-bθ²/2 + Σ_{k≥3} (b_k/k!)(iθ)^k)dθ,
collecting the b^{-2}-order terms (Gaussian moments μ8=105, μ10=945, μ12=10395),
with v_k=b_k/k!:
  δ2 = -15 v6/b³ + (210 v3v5 + 105 v4²)/(2b⁴) - (2835 v3²v4)/(6b⁵) + (10395 v3⁴)/(24b⁶).

VERIFIED:
- Poisson/e^z (all b_k=n): δ1=-1/(12n), δ2=1/(288n²) — matches 1/n! Stirling expansion.
- Involutions e^{z+z²/2} (b_k=r+2^{k-1}r², r(1+r)=n): δ1=-1/(6n) [matches InvolutionSecondOrder],
  δ2→1/(72n²); numeric check vs exact I_n/n!: residual/δ2_pred = 1.0036,1.0017,1.0011 (n=500,1k,2k) → 1.

LEAN TODO: saddleThirdPoly (integrand-level, b3..b6), gaussian_integral_saddleThirdPoly,
abstract coeff_thirdOrder_saddle (extend SecondOrderHAdmissible → ThirdOrder structure with
b5,b6 + third-order local L1 + tail), then instances (involution δ2=1/72, Bell, etc.).
