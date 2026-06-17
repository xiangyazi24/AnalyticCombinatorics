import AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-!
# The labelled-cycle count `(n-1)!` (F&S §II.2, the CYC logarithm)

The Ch2 cycle construction `CYC` is characterized at the EGF level by the ODE
`CYC(C)' = C'·SEQ(C)` together with a zero constant term
(`CombClass.egf_lcyc_unique`).  For the atomic class `Z` this pins the EGF down to
the **logarithm** `L(z) = log(1/(1-z)) = Σ_{n≥1} zⁿ/n` (`atom_lcyc_egf_eq_cycleEGFℚ`,
with `coeff n cycleEGFℚ = 1/n`).

This file records the resulting *combinatorial* closed form — the signature CYC
fact that an `n`-element labelled set admits exactly `(n-1)!` distinct cyclic
arrangements:

  `atom.lcyc.counts n = (n-1)!`  (`n ≥ 1`).

It is the integer shadow of the analytic identity `[zⁿ] log(1/(1-z)) = 1/n`
read through `[zⁿ] EGF = counts n / n!`, since `n!/n = (n-1)!`.
-/

open PowerSeries

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- **The labelled-cycle count.**  The number of cyclic arrangements of an
`n`-element labelled set is `(n-1)!` (for `n ≥ 1`) — the combinatorial form of the
CYC logarithm `log(1/(1-z))`, whose `n`-th EGF coefficient is `1/n`. -/
theorem atom_lcyc_counts_eq_factorial (n : ℕ) (hn : 1 ≤ n) :
    CombClass.atom.lcyc.counts n = (n - 1).factorial := by
  -- `[zⁿ] CYC(Z).egf = counts n / n!` equals `[zⁿ] log(1/(1-z)) = 1/n`.
  have hcoeff :
      (CombClass.atom.lcyc.counts n : ℚ) / (n.factorial : ℚ) = (n : ℚ)⁻¹ := by
    rw [← CombClass.coeff_egf, atom_lcyc_egf_eq_cycleEGFℚ, coeff_cycleEGFℚ]
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfac0 : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  -- `n! = n · (n-1)!`.
  have hfact : (n.factorial : ℚ) = (n : ℚ) * ((n - 1).factorial : ℚ) := by
    have hnat : n.factorial = n * (n - 1).factorial := by
      cases n with
      | zero => exact absurd hn (by norm_num)
      | succ m => rw [Nat.factorial_succ, Nat.succ_sub_one]
    exact_mod_cast hnat
  -- Solve `counts/n! = 1/n` for `counts`, then cast back to `ℕ`.
  rw [div_eq_iff hfac0] at hcoeff
  have key : (CombClass.atom.lcyc.counts n : ℚ) = ((n - 1).factorial : ℚ) := by
    rw [hcoeff, hfact, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  exact_mod_cast key

end AnalyticCombinatorics
