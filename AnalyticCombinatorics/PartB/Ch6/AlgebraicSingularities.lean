import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.AlgebraicSingularities


/-!
Finite tables around Chapter VI algebraic singularities.

The entries are bounded sanity checks for square-root singular behaviour,
Newton-Puiseux exponents, and algebraic specifications such as Catalan,
Motzkin, secondary structures, trees by bounded height, and series-parallel
network analogues.
-/

def catalanBySize : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786]

def catalanByPositiveSize : Fin 11 → ℕ :=
  ![1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786]

def catalanBySizeOneToTen : Fin 10 → ℕ :=
  ![1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]

def catalanBySizeTwoToEleven : Fin 10 → ℕ :=
  ![2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786]

def motzkinBySize : Fin 12 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, 5798]

def motzkinByPositiveSize : Fin 11 → ℕ :=
  ![1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, 5798]

def secondaryStructureByLength : Fin 12 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, 5798]

def binaryTreesHeightAtMostThree : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 6, 6, 4, 1, 0, 0, 0, 0]

def binaryTreesHeightAtMostFour : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 14, 26, 44, 69, 94, 114, 116, 94]

def seriesParallelNetworkCounts : Fin 10 → ℕ :=
  ![1, 2, 6, 22, 90, 394, 1806, 8558, 41586, 206098]

def seriesParallelCountsFirstNine : Fin 9 → ℕ :=
  ![1, 2, 6, 22, 90, 394, 1806, 8558, 41586]

def seriesParallelCountsNextNine : Fin 9 → ℕ :=
  ![2, 6, 22, 90, 394, 1806, 8558, 41586, 206098]

/-- Degrees of small algebraic equations in the unknown generating function. -/
def algebraicEquationDegrees : Fin 6 → ℕ :=
  ![2, 2, 2, 3, 2, 4]

/-- Puiseux denominator for the dominant local exponent: `2` means square-root. -/
def puiseuxExponentDenominator : Fin 6 → ℕ :=
  ![2, 2, 2, 3, 2, 2]

def catalanDominantGrowthBase : ℕ := 4

def motzkinDominantGrowthBase : ℕ := 3

def squareRootSingularFamilyCount : ℕ := 5

theorem catalan_initial_segment_strictly_below_four_power :
    ∀ i : Fin 11, catalanByPositiveSize i < catalanDominantGrowthBase ^ (i.val + 1) := by
  native_decide

theorem catalan_square_root_scaled_ratios_decrease :
    ∀ i : Fin 10,
      catalanBySizeTwoToEleven i * (i.val + 3) *
          catalanDominantGrowthBase ^ (i.val + 1) ≤
        catalanBySizeOneToTen i * (i.val + 2) *
          catalanDominantGrowthBase ^ (i.val + 2) := by
  native_decide

theorem motzkin_initial_segment_strictly_below_three_power :
    ∀ i : Fin 11, motzkinByPositiveSize i < motzkinDominantGrowthBase ^ (i.val + 1) := by
  native_decide

theorem motzkin_and_secondary_structure_tables_agree :
    ∀ i : Fin 12, secondaryStructureByLength i = motzkinBySize i := by
  native_decide

theorem height_four_refines_height_three :
    ∀ i : Fin 12, binaryTreesHeightAtMostThree i ≤ binaryTreesHeightAtMostFour i := by
  native_decide

theorem height_three_saturates_catalan_through_size_three :
    ∀ i : Fin 4, binaryTreesHeightAtMostThree (Fin.castLE (by native_decide) i) =
      catalanBySize (Fin.castLE (by native_decide) i) := by
  native_decide

theorem height_four_saturates_catalan_through_size_four :
    ∀ i : Fin 5, binaryTreesHeightAtMostFour (Fin.castLE (by native_decide) i) =
      catalanBySize (Fin.castLE (by native_decide) i) := by
  native_decide

theorem algebraic_degree_table_all_nontrivial :
    ∀ i : Fin 6, 2 ≤ algebraicEquationDegrees i := by
  native_decide

theorem square_root_cases_are_majority :
    4 ≤ squareRootSingularFamilyCount := by
  native_decide

theorem series_parallel_counts_grow_on_initial_window :
    ∀ i : Fin 9, seriesParallelCountsFirstNine i < seriesParallelCountsNextNine i := by
  native_decide



structure AlgebraicSingularitiesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlgebraicSingularitiesBudgetCertificate.controlled
    (c : AlgebraicSingularitiesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AlgebraicSingularitiesBudgetCertificate.budgetControlled
    (c : AlgebraicSingularitiesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AlgebraicSingularitiesBudgetCertificate.Ready
    (c : AlgebraicSingularitiesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlgebraicSingularitiesBudgetCertificate.size
    (c : AlgebraicSingularitiesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem algebraicSingularities_budgetCertificate_le_size
    (c : AlgebraicSingularitiesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAlgebraicSingularitiesBudgetCertificate :
    AlgebraicSingularitiesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAlgebraicSingularitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicSingularitiesBudgetCertificate.controlled,
      sampleAlgebraicSingularitiesBudgetCertificate]
  · norm_num [AlgebraicSingularitiesBudgetCertificate.budgetControlled,
      sampleAlgebraicSingularitiesBudgetCertificate]

example :
    sampleAlgebraicSingularitiesBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicSingularitiesBudgetCertificate.size := by
  apply algebraicSingularities_budgetCertificate_le_size
  constructor
  · norm_num [AlgebraicSingularitiesBudgetCertificate.controlled,
      sampleAlgebraicSingularitiesBudgetCertificate]
  · norm_num [AlgebraicSingularitiesBudgetCertificate.budgetControlled,
      sampleAlgebraicSingularitiesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAlgebraicSingularitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicSingularitiesBudgetCertificate.controlled,
      sampleAlgebraicSingularitiesBudgetCertificate]
  · norm_num [AlgebraicSingularitiesBudgetCertificate.budgetControlled,
      sampleAlgebraicSingularitiesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlgebraicSingularitiesBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicSingularitiesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AlgebraicSingularitiesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAlgebraicSingularitiesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAlgebraicSingularitiesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.AlgebraicSingularities
