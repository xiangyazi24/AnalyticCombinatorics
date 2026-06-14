import AnalyticCombinatorics.Ch2.EGF.LabelledCyc
import AnalyticCombinatorics.Ch2.EGF.LabelledSeq
import AnalyticCombinatorics.Ch2.EGF.SetExp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Ch2 §II.2 — The labelled cycle closed form `CYC(C) = log(1/(1-C))`

`LabelledCyc.lean` characterizes the labelled cycle EGF by its ODE
`CYC(C)' = C'·SEQ(C)` together with a zero constant term
(`egf_lcyc_ode`, `egf_lcyc_unique`). The literal F&S closed form is

  `CYC(C)(z) = log(1 / (1 - C(z)))`.

Mathlib has no formal-power-series logarithm, so we deliver this in the
equivalent **exponentiated** shape, which needs only `PowerSeries.exp`
(already used for `egf_set`):

  `exp(CYC(C)) = 1/(1 - C(z)) = SEQ(C)`.

Both `exp(CYC(C))` and `SEQ(C)` solve the linear ODE `G' = CYC(C)'·G` with
constant term `1`, hence coincide by `ode_unique`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- `SEQ(C)` satisfies `SEQ(C)' = C'·SEQ(C)²`, obtained by differentiating the
defining relation `SEQ(C)·(1 - C) = 1`. -/
theorem CombClass.egf_lseq_deriv (C : CombClass) (hC : C.counts 0 = 0) :
    d⁄dX ℚ C.lseq.egf = d⁄dX ℚ C.egf * C.lseq.egf * C.lseq.egf := by
  have hlseq : C.lseq.egf * (1 - C.egf) = 1 := CombClass.egf_lseq C hC
  rw [(d⁄dX ℚ).leibniz_of_mul_eq_one hlseq]
  simp only [map_sub, Derivation.map_one_eq_zero, zero_sub, smul_eq_mul,
    neg_mul, mul_neg, neg_neg]
  ring

/-- **Labelled cycle closed form** (exponentiated): `exp(CYC(C)) = SEQ(C)`,
i.e. `CYC(C)(z) = log(1 / (1 - C(z)))` (F&S §II.2). -/
theorem CombClass.exp_egf_lcyc (C : CombClass) (hC : C.counts 0 = 0) :
    (exp ℚ).subst C.lcyc.egf = C.lseq.egf := by
  have h0C : constantCoeff C.egf = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf, hC]; simp
  have hcyc0 : constantCoeff C.lcyc.egf = 0 := CombClass.constantCoeff_egf_lcyc C
  have hsubst : HasSubst C.lcyc.egf := by
    apply HasSubst.of_constantCoeff_zero'
    rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf]
    simp [CombClass.counts, CombClass.lcyc]
  -- `exp(CYC(C))` satisfies the chain-rule ODE `F' = CYC(C)'·F`.
  have hexp_ode :
      d⁄dX ℚ ((exp ℚ).subst C.lcyc.egf)
        = d⁄dX ℚ C.lcyc.egf * (exp ℚ).subst C.lcyc.egf := by
    rw [derivative_subst (hg := hsubst), derivative_exp]; ring
  -- The difference `H = exp(CYC(C)) - SEQ(C)` solves the homogeneous ODE.
  set H : ℚ⟦X⟧ := (exp ℚ).subst C.lcyc.egf - C.lseq.egf with hH
  have hode : d⁄dX ℚ H = (d⁄dX ℚ C.egf * C.lseq.egf) * H := by
    rw [hH, map_sub, hexp_ode, CombClass.egf_lcyc_ode C hC,
      CombClass.egf_lseq_deriv C hC]
    ring
  have h0subst : constantCoeff ((exp ℚ).subst C.lcyc.egf) = 1 := by
    change MvPowerSeries.constantCoeff (PowerSeries.subst C.lcyc.egf (PowerSeries.exp ℚ)) = 1
    rw [constantCoeff_subst hsubst, finsum_eq_single _ 0]
    · simp
    · intro d hd
      have hpow : MvPowerSeries.constantCoeff (C.lcyc.egf ^ d) = 0 := by
        change constantCoeff (C.lcyc.egf ^ d) = 0
        rw [map_pow, hcyc0, zero_pow hd]
      rw [hpow, smul_zero]
  have h0lseq : constantCoeff C.lseq.egf = 1 := by
    have h : constantCoeff (C.lseq.egf * (1 - C.egf)) = constantCoeff (1 : ℚ⟦X⟧) :=
      congrArg _ (CombClass.egf_lseq C hC)
    rwa [map_mul, map_sub, map_one, h0C, sub_zero, mul_one] at h
  have h0 : constantCoeff H = 0 := by
    rw [hH, map_sub, h0subst, h0lseq, sub_self]
  have hHzero : H = 0 := ode_unique hode h0
  rw [hH] at hHzero
  exact sub_eq_zero.mp hHzero

end AnalyticCombinatorics.Ch1

-- Axiom audit (must be exactly {propext, Classical.choice, Quot.sound}):
#print axioms AnalyticCombinatorics.Ch1.CombClass.egf_lseq_deriv
#print axioms AnalyticCombinatorics.Ch1.CombClass.exp_egf_lcyc
