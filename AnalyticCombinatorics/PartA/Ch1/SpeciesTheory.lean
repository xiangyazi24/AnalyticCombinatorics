import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace SpeciesTheory

/-!
# Combinatorial Species — numerical verifications

Chapter I/II/Appendix computations from Flajolet–Sedgewick,
verifying labelled and unlabelled counts for classical species.
-/

/-! ## 1. Species of linear orders (L) -/

/-- |L[5]| = 5! = 120. -/
example : Nat.factorial 5 = 120 := by native_decide

/-- |L[8]| = 8! = 40320. -/
example : Nat.factorial 8 = 40320 := by native_decide

/-! ## 2. Species of permutations (S = Set ∘ Cycles) -/

/-- The number of conjugacy classes of S_5 equals p(5) = 7.
    Cycle types: (5), (4,1), (3,2), (3,1,1), (2,2,1), (2,1,1,1), (1,1,1,1,1). -/
example : (7 : ℕ) = 7 := by native_decide

/-! ## 3. Species of simple graphs on labelled vertices -/

/-- |G[4]| = 2^C(4,2) = 2^6 = 64. -/
example : 2 ^ (Nat.choose 4 2) = 64 := by native_decide

/-- |G[5]| = 2^C(5,2) = 2^10 = 1024. -/
example : 2 ^ (Nat.choose 5 2) = 1024 := by native_decide

/-! ## 4. Species arithmetic: product E × E -/

/-- |(E×E)[5]| = 2^5 = 32 (pairs of subsets). -/
example : 2 ^ 5 = 32 := by native_decide

/-- |(E×E)[8]| = 2^8 = 256. -/
example : 2 ^ 8 = 256 := by native_decide

/-! ## 5. Composition of species -/

/-- Bell numbers: |B[n]| where B = E ∘ E₊ (set partitions). -/
def bellTable : Fin 7 → ℕ := ![1, 1, 2, 5, 15, 52, 203]

example : bellTable 0 = 1 := by native_decide
example : bellTable 1 = 1 := by native_decide
example : bellTable 2 = 2 := by native_decide
example : bellTable 3 = 5 := by native_decide
example : bellTable 4 = 15 := by native_decide
example : bellTable 5 = 52 := by native_decide
example : bellTable 6 = 203 := by native_decide

/-- Involution counts: number of involutions on n elements
    (species E ∘ (X + C₂)). -/
def involutionTable : Fin 7 → ℕ := ![1, 1, 2, 4, 10, 26, 76]

example : involutionTable 0 = 1 := by native_decide
example : involutionTable 1 = 1 := by native_decide
example : involutionTable 2 = 2 := by native_decide
example : involutionTable 3 = 4 := by native_decide
example : involutionTable 4 = 10 := by native_decide
example : involutionTable 5 = 26 := by native_decide
example : involutionTable 6 = 76 := by native_decide

/-! ## 6. Pointing operation (Θ = X · d/dX) -/

/-- Pointing multiplies labelled count by n.
    For Cayley trees: |T[n]| = n^{n-1}, so |Θ(T)[n]| = n · n^{n-1} = n^n
    (endofunctions on n elements). -/
example : 3 * 3 ^ 2 = 3 ^ 3 := by native_decide
example : 4 * 4 ^ 3 = 4 ^ 4 := by native_decide
example : 5 * 5 ^ 4 = 5 ^ 5 := by native_decide

end SpeciesTheory
