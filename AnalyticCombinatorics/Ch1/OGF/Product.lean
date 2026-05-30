import AnalyticCombinatorics.Ch1.OGF.Defs
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Ch1 §I.2 — The Cartesian product construction

Flajolet & Sedgewick, Part A, Chapter I, §I.2, the product construction, the
heart of the symbolic method. If `A = B × C` (an object of size `n` is an
ordered pair `(β, γ)` with `|β| + |γ| = n`), then

  `Aₙ = ∑_{k=0}^{n} Bₖ · C_{n-k}`   (a convolution),

and therefore the OGFs multiply:

  **`(B × C)(z) = B(z) · C(z)`**   (part of F&S Theorem I.1).

The combinatorial content is the `Fintype.card` convolution identity
`counts_prod`, proved from `Fintype.card_sigma` / `Fintype.card_prod`. The
generating-function identity `ogf_prod` then follows from `PowerSeries.coeff_mul`
(the Cauchy product) after reconciling the `Finset.antidiagonal` indexing with
the `Fin (n+1)` indexing of the product class.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- The Cartesian product `B × C` (F&S §I.2): an object of size `n` is a pair
`(β, γ)` with `|β| + |γ| = n`, enumerated as `Σ k ≤ n, B_k × C_{n-k}`. -/
def CombClass.prod (C D : CombClass) : CombClass where
  Obj n := Σ k : Fin (n + 1), C.Obj k × D.Obj (n - k)
  finObj _ := inferInstance

/-- Counting sequences convolve: `(B × C)ₙ = ∑_{k≤n} Bₖ · C_{n-k}`. The genuine
combinatorial content, from `Fintype.card_sigma` and `Fintype.card_prod`. -/
@[simp] lemma CombClass.counts_prod (C D : CombClass) (n : ℕ) :
    (C.prod D).counts n = ∑ k : Fin (n + 1), C.counts k * D.counts (n - k) := by
  change Fintype.card (Σ k : Fin (n + 1), C.Obj k × D.Obj (n - k)) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_prod]
  rfl

/-- **Product rule** (F&S Theorem I.1): `(B × C)(z) = B(z) · C(z)`. -/
theorem CombClass.ogf_prod (C D : CombClass) :
    (C.prod D).ogf = C.ogf * D.ogf := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_prod, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Fin.sum_univ_eq_sum_range (fun k => C.counts k * D.counts (n - k)) (n + 1)]
  push_cast
  simp [CombClass.coeff_ogf]

/-- The neutral class `ε` is a left identity for the product, at the level of
generating functions: `ε × C` has OGF `1 · C(z) = C(z)`. -/
lemma CombClass.ogf_neutral_prod (C : CombClass) :
    (CombClass.neutral.prod C).ogf = C.ogf := by
  rw [CombClass.ogf_prod, CombClass.ogf_neutral, one_mul]

end AnalyticCombinatorics.Ch1
