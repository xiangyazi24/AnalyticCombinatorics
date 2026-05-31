import AnalyticCombinatorics.Ch2.EGF.LabelledSetExp
import AnalyticCombinatorics.Ch2.EGF.LabelledSeq
import AnalyticCombinatorics.Ch1.OGF.Sequence
import AnalyticCombinatorics.Ch1.OGF.Fibonacci

/-!
# Ch2 §II.3 — Applications of the labelled symbolic method

Flajolet & Sedgewick, Part A, Chapter II, §II.3. Using the labelled set and
sequence transfers on the positive-integer ("urn"/nonempty-block) class `ℙ`
(one object of each size `n ≥ 1`, EGF `e^z - 1`):

* set partitions / **Bell numbers** `SET(ℙ)`, EGF `exp(e^z - 1)`;
* **surjections** `SEQ(ℙ)`, EGF `1/(2 - e^z)`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The EGF of the positive-integer (nonempty-block) class is `e^z - 1`. -/
theorem CombClass.egf_posInt : CombClass.posInt.egf = PowerSeries.exp ℚ - 1 := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_posInt, map_sub, coeff_exp, coeff_one]
  rcases n with _ | m <;> simp

/-- **Set partitions / Bell numbers** (F&S §II.3): `SET(ℙ)(z) = exp(e^z - 1)`. -/
theorem CombClass.egf_bell :
    CombClass.posInt.set.egf = (PowerSeries.exp ℚ).subst (PowerSeries.exp ℚ - 1) := by
  rw [CombClass.egf_set _ (by simp [CombClass.counts_posInt]), CombClass.egf_posInt]

/-- **Surjections** (F&S §II.3): `SEQ(ℙ)(z)·(2 - e^z) = 1`, i.e. `1/(2 - e^z)`. -/
theorem CombClass.egf_surjections :
    CombClass.posInt.lseq.egf * (1 - (PowerSeries.exp ℚ - 1)) = 1 := by
  have h := CombClass.egf_lseq CombClass.posInt (by simp [CombClass.counts_posInt])
  rwa [CombClass.egf_posInt] at h

/-- The EGF of the "singletons-and-pairs" class is `z + z²/2`. -/
theorem CombClass.egf_parts12_egf :
    CombClass.parts12.egf = X + (2⁻¹ : ℚ) • X ^ 2 := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_parts12, map_add, coeff_X, map_smul, coeff_X_pow,
    smul_eq_mul]
  rcases n with _ | _ | _ | m <;> norm_num [Nat.factorial] <;> omega

/-- **Involutions** (F&S §II.3): an involution is a set of fixed points and
transpositions, `SET(ℙ₁₂)` where `ℙ₁₂` has one object each of size 1 and 2.
Its EGF is `exp(z + z²/2)`. -/
theorem CombClass.egf_involutions :
    CombClass.parts12.set.egf = (PowerSeries.exp ℚ).subst (X + (2⁻¹ : ℚ) • X ^ 2) := by
  rw [CombClass.egf_set _ (by simp [CombClass.counts_parts12]), CombClass.egf_parts12_egf]

end AnalyticCombinatorics.Ch1
