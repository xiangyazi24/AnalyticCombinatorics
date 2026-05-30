import AnalyticCombinatorics.Ch1.OGF.Product

/-!
# Ch1 §I.2–I.3 — Cartesian powers and words over a finite alphabet

Flajolet & Sedgewick, Part A, Chapter I. Iterating the product construction gives
the `k`-fold Cartesian power `C^k = C × C × ⋯ × C`, with OGF `C(z)^k` (an immediate
induction from the binary product rule `ogf_prod`). As the standard application,
words of length `k` over an alphabet of `a` letters form `(a·Z)^k`, with OGF
`(a z)^k` (so there are `a^k` of them), recovering F&S §I.3.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The `k`-fold Cartesian power `C^k = C × (C × (⋯))` (F&S §I.2). -/
def CombClass.prodPow (C : CombClass) : ℕ → CombClass
  | 0 => CombClass.neutral
  | (k + 1) => C.prod (C.prodPow k)

/-- **Power rule**: `(C^k)(z) = C(z)^k`. -/
@[simp] theorem CombClass.ogf_prodPow (C : CombClass) (k : ℕ) :
    (C.prodPow k).ogf = C.ogf ^ k := by
  induction k with
  | zero => simp [CombClass.prodPow, CombClass.ogf_neutral]
  | succ k ih => rw [CombClass.prodPow, CombClass.ogf_prod, ih, pow_succ']

/-- The alphabet class on `a` letters: `a` distinct objects of size `1`
(F&S §I.3). Its OGF is `a·z`. -/
def CombClass.alphabet (a : ℕ) : CombClass where
  Obj n := Fin (if n = 1 then a else 0)
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_alphabet (a n : ℕ) :
    (CombClass.alphabet a).counts n = if n = 1 then a else 0 :=
  Fintype.card_fin _

/-- The OGF of an `a`-letter alphabet is `a·z`. -/
theorem CombClass.ogf_alphabet (a : ℕ) :
    (CombClass.alphabet a).ogf = (a : ℕ) • X := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_alphabet, map_nsmul, coeff_X]
  by_cases h : n = 1 <;> simp [h]

/-- **Words over a finite alphabet** (F&S §I.3): the words of length `k` over an
`a`-letter alphabet form `(a·Z)^k`, with OGF `(a z)^k`. -/
theorem CombClass.ogf_words (a k : ℕ) :
    ((CombClass.alphabet a).prodPow k).ogf = ((a : ℕ) • X : ℚ⟦X⟧) ^ k := by
  rw [CombClass.ogf_prodPow, CombClass.ogf_alphabet]

end AnalyticCombinatorics.Ch1
