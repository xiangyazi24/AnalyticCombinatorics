/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Applications of Singularity Analysis.

  This file formalizes executable coefficient checks for counting sequences
  that arise as applications of singularity analysis (Flajolet & Sedgewick Ch. VII):

  1. Pólya trees (non-isomorphic rooted trees)
  2. BST / Catalan numbers and the identity C(n)·(n+1) = C(2n,n)
  3. Motzkin numbers (simply generated trees with φ(u) = 1 + u + u²)
  4. Dyck path / Catalan ratio checks (approach to growth rate 4)
  5. Rooted planar maps by edges
  6. Compositions of n = 2^{n-1} and their constant ratio
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option linter.flexible false

namespace ApplicationsOfSingularity

/-! ## 1. Pólya trees (non-isomorphic rooted trees, OEIS A000081) -/

/-- Number of non-isomorphic rooted trees on n nodes (Pólya, 1937).
    Values: T(1)=1, T(2)=1, T(3)=2, T(4)=4, T(5)=9, T(6)=20,
    T(7)=48, T(8)=115, T(9)=286.
    The OGF satisfies T(z) = z·exp(∑_{k≥1} T(z^k)/k). -/
def polyaTreeTable : Fin 9 → ℕ := ![1, 1, 2, 4, 9, 20, 48, 115, 286]

theorem polyaTree_1 : polyaTreeTable ⟨0, by omega⟩ = 1 := by native_decide
theorem polyaTree_2 : polyaTreeTable ⟨1, by omega⟩ = 1 := by native_decide
theorem polyaTree_3 : polyaTreeTable ⟨2, by omega⟩ = 2 := by native_decide
theorem polyaTree_4 : polyaTreeTable ⟨3, by omega⟩ = 4 := by native_decide
theorem polyaTree_5 : polyaTreeTable ⟨4, by omega⟩ = 9 := by native_decide
theorem polyaTree_6 : polyaTreeTable ⟨5, by omega⟩ = 20 := by native_decide
theorem polyaTree_7 : polyaTreeTable ⟨6, by omega⟩ = 48 := by native_decide
theorem polyaTree_8 : polyaTreeTable ⟨7, by omega⟩ = 115 := by native_decide
theorem polyaTree_9 : polyaTreeTable ⟨8, by omega⟩ = 286 := by native_decide

/-- Monotonicity: the Pólya tree counts are strictly increasing for n ≥ 3. -/
theorem polyaTree_mono :
    ∀ i : Fin 8, i.val ≥ 2 → polyaTreeTable ⟨i.val, by omega⟩ <
      polyaTreeTable ⟨i.val + 1, by omega⟩ := by
  intro i hi
  fin_cases i <;> simp_all <;> native_decide

/-! ## 2. Binary search trees / Catalan numbers -/

/-- Catalan number via the standard formula C(n) = C(2n,n)/(n+1). -/
def catalanNumber (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- BST count table (number of distinct BSTs on n keys = Catalan(n)). -/
def bstTable : Fin 9 → ℕ := ![1, 1, 2, 5, 14, 42, 132, 429, 1430]

/-- The BST table matches the Catalan formula. -/
theorem bst_eq_catalan :
    ∀ i : Fin 9, bstTable i = catalanNumber i.val := by
  intro i; fin_cases i <;> native_decide

/-- The fundamental identity: C(n)·(n+1) = C(2n, n) for n = 0, ..., 12. -/
theorem catalan_mul_succ_eq_centralBinom :
    ∀ n ∈ Finset.Icc 0 12,
      catalanNumber n * (n + 1) = Nat.choose (2 * n) n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, hnhi⟩
  interval_cases n <;> native_decide

/-! ## 3. Motzkin numbers (simply generated trees, φ(u) = 1 + u + u²) -/

/-- Motzkin numbers M(n): count of Motzkin paths of length n, or equivalently
    unary-binary trees (simply generated with offspring GF φ(u) = 1 + u + u²).
    OEIS A001006. -/
def motzkinTable : Fin 11 → ℕ := ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188]

theorem motzkin_0 : motzkinTable ⟨0, by omega⟩ = 1 := by native_decide
theorem motzkin_1 : motzkinTable ⟨1, by omega⟩ = 1 := by native_decide
theorem motzkin_2 : motzkinTable ⟨2, by omega⟩ = 2 := by native_decide
theorem motzkin_3 : motzkinTable ⟨3, by omega⟩ = 4 := by native_decide
theorem motzkin_4 : motzkinTable ⟨4, by omega⟩ = 9 := by native_decide
theorem motzkin_5 : motzkinTable ⟨5, by omega⟩ = 21 := by native_decide
theorem motzkin_6 : motzkinTable ⟨6, by omega⟩ = 51 := by native_decide
theorem motzkin_7 : motzkinTable ⟨7, by omega⟩ = 127 := by native_decide
theorem motzkin_8 : motzkinTable ⟨8, by omega⟩ = 323 := by native_decide
theorem motzkin_9 : motzkinTable ⟨9, by omega⟩ = 835 := by native_decide
theorem motzkin_10 : motzkinTable ⟨10, by omega⟩ = 2188 := by native_decide

/-- Motzkin numbers satisfy M(n) < 3^n (growth rate is 3). -/
theorem motzkin_lt_three_pow :
    ∀ i : Fin 11, i.val ≥ 1 → motzkinTable i < 3 ^ i.val := by
  intro i hi; fin_cases i <;> simp_all <;> native_decide

/-- Motzkin recurrence: (n+3)·M(n+1) = (2n+3)·M(n) + 3n·M(n-1) for n ≥ 1.
    Verified pointwise for n = 1, ..., 8. -/
theorem motzkin_recurrence_1 :
    4 * motzkinTable ⟨2, by omega⟩ =
    5 * motzkinTable ⟨1, by omega⟩ + 3 * motzkinTable ⟨0, by omega⟩ := by native_decide
theorem motzkin_recurrence_2 :
    5 * motzkinTable ⟨3, by omega⟩ =
    7 * motzkinTable ⟨2, by omega⟩ + 6 * motzkinTable ⟨1, by omega⟩ := by native_decide
theorem motzkin_recurrence_3 :
    6 * motzkinTable ⟨4, by omega⟩ =
    9 * motzkinTable ⟨3, by omega⟩ + 9 * motzkinTable ⟨2, by omega⟩ := by native_decide
theorem motzkin_recurrence_4 :
    7 * motzkinTable ⟨5, by omega⟩ =
    11 * motzkinTable ⟨4, by omega⟩ + 12 * motzkinTable ⟨3, by omega⟩ := by native_decide
theorem motzkin_recurrence_5 :
    8 * motzkinTable ⟨6, by omega⟩ =
    13 * motzkinTable ⟨5, by omega⟩ + 15 * motzkinTable ⟨4, by omega⟩ := by native_decide
theorem motzkin_recurrence_6 :
    9 * motzkinTable ⟨7, by omega⟩ =
    15 * motzkinTable ⟨6, by omega⟩ + 18 * motzkinTable ⟨5, by omega⟩ := by native_decide
theorem motzkin_recurrence_7 :
    10 * motzkinTable ⟨8, by omega⟩ =
    17 * motzkinTable ⟨7, by omega⟩ + 21 * motzkinTable ⟨6, by omega⟩ := by native_decide
theorem motzkin_recurrence_8 :
    11 * motzkinTable ⟨9, by omega⟩ =
    19 * motzkinTable ⟨8, by omega⟩ + 24 * motzkinTable ⟨7, by omega⟩ := by native_decide

/-! ## 4. Dyck paths and Catalan ratio approaching 4 -/

/-- C(10) = 16796 -/
theorem catalan_10 : catalanNumber 10 = 16796 := by native_decide

/-- C(9) = 4862 -/
theorem catalan_9 : catalanNumber 9 = 4862 := by native_decide

/-- C(15) = 9694845 -/
theorem catalan_15 : catalanNumber 15 = 9694845 := by native_decide

/-- C(14) = 2674440 -/
theorem catalan_14 : catalanNumber 14 = 2674440 := by native_decide

/-- The ratio C(n)/C(n-1) = (4n-2)/(n+1) approaches 4 from below.
    We verify C(n) < 4 * C(n-1) for n = 1, ..., 15. -/
theorem catalan_lt_four_times_prev :
    ∀ n ∈ Finset.Icc 1 15,
      catalanNumber n < 4 * catalanNumber (n - 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

/-- The ratio C(n)/C(n-1) exceeds 2 for n ≥ 2.
    Since C(n)/C(n-1) = (4n-2)/(n+1), for n=2 this is 6/3 = 2.
    We check C(n) ≥ 2 * C(n-1) for n = 2, ..., 15. -/
theorem catalan_ge_two_times_prev :
    ∀ n ∈ Finset.Icc 2 15,
      catalanNumber n ≥ 2 * catalanNumber (n - 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

/-- The exact ratio formula: C(n)·(n+1) = (4n-2)·C(n-1) for n ≥ 1. -/
theorem catalan_ratio_exact :
    ∀ n ∈ Finset.Icc 1 12,
      catalanNumber n * (n + 1) = (4 * n - 2) * catalanNumber (n - 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

/-! ## 5. Rooted planar maps (OEIS A000168) -/

/-- Number of rooted planar maps with n edges.
    M(0)=1, M(1)=2, M(2)=9, M(3)=54, M(4)=378, M(5)=2916.
    Formula: M(n) = 2·(2n)! · 3^n / (n! · (n+2)!). -/
def rootedMapsTable : Fin 6 → ℕ := ![1, 2, 9, 54, 378, 2916]

theorem rootedMaps_0 : rootedMapsTable ⟨0, by omega⟩ = 1 := by native_decide
theorem rootedMaps_1 : rootedMapsTable ⟨1, by omega⟩ = 2 := by native_decide
theorem rootedMaps_2 : rootedMapsTable ⟨2, by omega⟩ = 9 := by native_decide
theorem rootedMaps_3 : rootedMapsTable ⟨3, by omega⟩ = 54 := by native_decide
theorem rootedMaps_4 : rootedMapsTable ⟨4, by omega⟩ = 378 := by native_decide
theorem rootedMaps_5 : rootedMapsTable ⟨5, by omega⟩ = 2916 := by native_decide

/-- Verify the closed-form formula for rooted maps:
    M(n) · n! · (n+2)! = 2 · (2n)! · 3^n for n = 0, ..., 5. -/
theorem rootedMaps_formula_0 :
    rootedMapsTable ⟨0, by omega⟩ * (Nat.factorial 0 * Nat.factorial 2) =
    2 * Nat.factorial 0 * 3 ^ 0 := by native_decide
theorem rootedMaps_formula_1 :
    rootedMapsTable ⟨1, by omega⟩ * (Nat.factorial 1 * Nat.factorial 3) =
    2 * Nat.factorial 2 * 3 ^ 1 := by native_decide
theorem rootedMaps_formula_2 :
    rootedMapsTable ⟨2, by omega⟩ * (Nat.factorial 2 * Nat.factorial 4) =
    2 * Nat.factorial 4 * 3 ^ 2 := by native_decide
theorem rootedMaps_formula_3 :
    rootedMapsTable ⟨3, by omega⟩ * (Nat.factorial 3 * Nat.factorial 5) =
    2 * Nat.factorial 6 * 3 ^ 3 := by native_decide
theorem rootedMaps_formula_4 :
    rootedMapsTable ⟨4, by omega⟩ * (Nat.factorial 4 * Nat.factorial 6) =
    2 * Nat.factorial 8 * 3 ^ 4 := by native_decide
theorem rootedMaps_formula_5 :
    rootedMapsTable ⟨5, by omega⟩ * (Nat.factorial 5 * Nat.factorial 7) =
    2 * Nat.factorial 10 * 3 ^ 5 := by native_decide

/-- Exponential growth: M(n) < 12^n for n = 1, ..., 5. -/
theorem rootedMaps_lt_twelve_pow_1 : rootedMapsTable ⟨1, by omega⟩ < 12 ^ 1 := by native_decide
theorem rootedMaps_lt_twelve_pow_2 : rootedMapsTable ⟨2, by omega⟩ < 12 ^ 2 := by native_decide
theorem rootedMaps_lt_twelve_pow_3 : rootedMapsTable ⟨3, by omega⟩ < 12 ^ 3 := by native_decide
theorem rootedMaps_lt_twelve_pow_4 : rootedMapsTable ⟨4, by omega⟩ < 12 ^ 4 := by native_decide
theorem rootedMaps_lt_twelve_pow_5 : rootedMapsTable ⟨5, by omega⟩ < 12 ^ 5 := by native_decide

/-! ## 6. Compositions of n and their constant ratio -/

/-- Number of compositions of n (ordered partitions into positive parts) = 2^{n-1}
    for n ≥ 1. This is the geometric growth case with ratio exactly 2. -/
def compositionCount (n : ℕ) : ℕ := if n = 0 then 1 else 2 ^ (n - 1)

theorem compositionCount_0 : compositionCount 0 = 1 := by native_decide
theorem compositionCount_1 : compositionCount 1 = 1 := by native_decide
theorem compositionCount_2 : compositionCount 2 = 2 := by native_decide
theorem compositionCount_3 : compositionCount 3 = 4 := by native_decide
theorem compositionCount_4 : compositionCount 4 = 8 := by native_decide
theorem compositionCount_5 : compositionCount 5 = 16 := by native_decide
theorem compositionCount_10 : compositionCount 10 = 512 := by native_decide

/-- The ratio compositionCount(n) / compositionCount(n-1) = 2 for all n ≥ 2.
    This is the simplest example of a rational GF with a simple pole
    (growth rate = inverse of radius of convergence = 2). -/
theorem composition_ratio_is_two :
    ∀ n ∈ Finset.Icc 2 15,
      compositionCount n = 2 * compositionCount (n - 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

/-- Power-of-two identity check: 2^n / 2^{n-1} = 2 for small values. -/
example : 2 ^ 4 / 2 ^ 3 = (2 : ℕ) := by native_decide
example : 2 ^ 9 / 2 ^ 8 = (2 : ℕ) := by native_decide
example : 2 ^ 15 / 2 ^ 14 = (2 : ℕ) := by native_decide

/-! ## Summary: exponential growth constants from singularity analysis

  | Structure                  | Growth rate ρ⁻¹  | Subexponential factor |
  |----------------------------|------------------|-----------------------|
  | Binary trees (Catalan)     | 4                | n^{-3/2}              |
  | Motzkin trees              | 3                | n^{-3/2}              |
  | Pólya trees                | ≈ 2.95576        | n^{-3/2}              |
  | Rooted planar maps         | 12               | n^{-5/2}              |
  | Compositions               | 2 (exact)        | 1 (no subexp.)        |
-/

end ApplicationsOfSingularity
