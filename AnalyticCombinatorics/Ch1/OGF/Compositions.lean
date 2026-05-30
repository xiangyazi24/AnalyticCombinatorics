import AnalyticCombinatorics.Ch1.OGF.Sequence

/-!
# Ch1 §I.3 — The generating function of integer compositions

Flajolet & Sedgewick, Part A, Chapter I, §I.3. There are `2^{n-1}` compositions
of `n ≥ 1` (Mathlib's `composition_card`), so their ordinary generating function
is

  `C(z) = ∑ₙ 2^{n-1} zⁿ = (1 - z)/(1 - 2z)`,

which we state in polynomial form as `C(z)·(1 - 2z) = 1 - z`. Mathlib has the
counting result but not this generating function, so the identity is new content;
it is the closed form predicted by the symbolic method via `compositions = SEQ(ℙ)`
(see `counts_seq_posInt` in `Sequence.lean`).
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma CombClass.coeff_ogf_compositions (n : ℕ) :
    coeff n CombClass.compositions.ogf = (2 ^ (n - 1) : ℚ) := by
  rw [CombClass.coeff_ogf, CombClass.counts_compositions]
  push_cast
  ring

/-- **OGF of integer compositions** (F&S §I.3): `C(z)·(1 - 2z) = 1 - z`, i.e.
`C(z) = (1 - z)/(1 - 2z)`. -/
theorem CombClass.ogf_compositions :
    CombClass.compositions.ogf * (1 - 2 * X) = 1 - X := by
  have expand : CombClass.compositions.ogf * (1 - 2 * X)
      = CombClass.compositions.ogf
        - CombClass.compositions.ogf * X - CombClass.compositions.ogf * X := by ring
  rw [expand]
  ext n
  rcases n with _ | _ | k
  · -- n = 0
    simp [map_sub, coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X]
  · -- n = 1
    simp [map_sub, coeff_succ_mul_X, coeff_one, coeff_X]
  · -- n = k + 2
    simp only [map_sub, coeff_succ_mul_X, CombClass.coeff_ogf_compositions,
      coeff_one, coeff_X, Nat.add_sub_cancel, pow_succ]
    norm_num
    ring

end AnalyticCombinatorics.Ch1
