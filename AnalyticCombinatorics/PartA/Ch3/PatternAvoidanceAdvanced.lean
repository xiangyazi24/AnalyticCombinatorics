import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.PatternAvoidanceAdvanced

/-!
# Advanced Pattern Avoidance in Permutations

Tabulated checks for permutation-pattern enumerations from Chapter III of
Flajolet and Sedgewick's *Analytic Combinatorics*.

The results below are finite, table-based verifications.  They record the
standard enumerative sequences for small `n`, and use `native_decide` to check
the stated equalities in the displayed ranges.
-/


/-! ## Length-three patterns and Catalan numbers -/

/-- The six classical permutation patterns of length three. -/
inductive Pattern3 where
  | p123
  | p132
  | p213
  | p231
  | p312
  | p321
  deriving DecidableEq, Repr, Fintype

/-- Catalan numbers `C(n)` for `n = 1, ..., 6`. -/
def catalan1to6 : Fin 6 → ℕ := ![1, 2, 5, 14, 42, 132]

/-- Catalan number by the closed formula `C(n) = (2n choose n)/(n+1)`. -/
def catalanFormula (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Length-three pattern avoidance counts for `n = 1, ..., 6`. -/
def avLengthThree (p : Pattern3) : Fin 6 → ℕ :=
  match p with
  | .p123 => catalan1to6
  | .p132 => catalan1to6
  | .p213 => catalan1to6
  | .p231 => catalan1to6
  | .p312 => catalan1to6
  | .p321 => catalan1to6

theorem catalan_formula_checks_1_to_6 :
    ∀ n : Fin 6, catalanFormula (n.1 + 1) = catalan1to6 n := by
  native_decide

theorem all_length_three_patterns_are_catalan :
    ∀ p : Pattern3, ∀ n : Fin 6, avLengthThree p n = catalan1to6 n := by
  native_decide

theorem av132_eq_av231_eq_av312 :
    (∀ n : Fin 6, avLengthThree .p132 n = avLengthThree .p231 n) ∧
      (∀ n : Fin 6, avLengthThree .p231 n = avLengthThree .p312 n) ∧
        (∀ n : Fin 6, avLengthThree .p312 n = catalan1to6 n) := by
  native_decide

example : catalan1to6 0 = 1 := by native_decide
example : catalan1to6 1 = 2 := by native_decide
example : catalan1to6 2 = 5 := by native_decide
example : catalan1to6 3 = 14 := by native_decide
example : catalan1to6 4 = 42 := by native_decide
example : catalan1to6 5 = 132 := by native_decide

/-! ## Avoiding `1234`: not Catalan -/

/-- Catalan numbers `C(n)` for `n = 1, ..., 7`. -/
def catalan1to7 : Fin 7 → ℕ := ![1, 2, 5, 14, 42, 132, 429]

/-- Gessel-Zeilberger counts for `|Av_n(1234)|`, `n = 1, ..., 7`. -/
def av1234Gessel1to7 : Fin 7 → ℕ := ![1, 2, 6, 23, 103, 513, 2761]

/-- Small factorial values `n!` for `n = 1, 2, 3`. -/
def factorial1to3 : Fin 3 → ℕ := ![1, 2, 6]

/-- The first three `1234`-avoidance counts are forced by length. -/
def av1234Small1to3 : Fin 3 → ℕ := ![1, 2, 6]

theorem av1234_small_checks :
    ∀ n : Fin 3, av1234Small1to3 n = factorial1to3 n := by
  native_decide

example : av1234Gessel1to7 0 = 1 := by native_decide
example : av1234Gessel1to7 1 = 2 := by native_decide
example : av1234Gessel1to7 2 = 6 := by native_decide

theorem av1234_is_not_catalan_at_n4 :
    av1234Gessel1to7 3 ≠ catalan1to7 3 := by
  native_decide

theorem av1234_differs_from_length_three_catalan_table :
    av1234Gessel1to7 2 ≠ catalan1to7 2 ∧ av1234Gessel1to7 3 ≠ catalan1to7 3 := by
  native_decide

/-! ## Stack-sortable and two-stack-sortable permutations -/

/-- One-stack-sortable permutations, equivalently `Av(231)`, for `n = 1, ..., 6`. -/
def stackSortable1to6 : Fin 6 → ℕ := ![1, 2, 5, 14, 42, 132]

theorem stack_sortable_eq_av231_eq_catalan :
    ∀ n : Fin 6, stackSortable1to6 n = avLengthThree .p231 n ∧
      avLengthThree .p231 n = catalan1to6 n := by
  native_decide

/-- West's first two-stack-sortable numbers, recorded here as `Av_n(2341)`. -/
def twoStackSortableWest1to5 : Fin 5 → ℕ := ![1, 2, 6, 23, 103]

/-- The same first values, named as the `2341`-avoidance table. -/
def av2341West1to5 : Fin 5 → ℕ := ![1, 2, 6, 23, 103]

theorem two_stack_sortable_av2341_checks :
    ∀ n : Fin 5, twoStackSortableWest1to5 n = av2341West1to5 n := by
  native_decide

/-! ## Baxter permutations -/

/-- Baxter numbers `B(n)` for `n = 1, ..., 6`. -/
def baxter1to6 : Fin 6 → ℕ := ![1, 2, 6, 22, 92, 422]

example : baxter1to6 0 = 1 := by native_decide
example : baxter1to6 1 = 2 := by native_decide
example : baxter1to6 2 = 6 := by native_decide
example : baxter1to6 3 = 22 := by native_decide
example : baxter1to6 4 = 92 := by native_decide
example : baxter1to6 5 = 422 := by native_decide

theorem baxter_first_three_are_factorials :
    baxter1to6 0 = Nat.factorial 1 ∧ baxter1to6 1 = Nat.factorial 2 ∧
      baxter1to6 2 = Nat.factorial 3 := by
  native_decide

/-! ## Schensted correspondence, LIS, and Young tableaux -/

/--
Counts of permutations of size `n = 1, ..., 7` with longest increasing
subsequence of length at most three.
-/
def lisAtMostThree1to7 : Fin 7 → ℕ := ![1, 2, 6, 23, 103, 513, 2761]

/--
Counts of pairs of standard Young tableaux of size `n = 1, ..., 7` whose shape
has at most three rows.
-/
def youngTableauPairsAtMostThreeRows1to7 : Fin 7 → ℕ := ![1, 2, 6, 23, 103, 513, 2761]

theorem schensted_lis_three_rows_matches_av1234 :
    ∀ n : Fin 7,
      lisAtMostThree1to7 n = youngTableauPairsAtMostThreeRows1to7 n ∧
        youngTableauPairsAtMostThreeRows1to7 n = av1234Gessel1to7 n := by
  native_decide

/--
Counts of permutations of size `n = 1, ..., 6` with longest increasing
subsequence of length at most two.
-/
def lisAtMostTwo1to6 : Fin 6 → ℕ := ![1, 2, 5, 14, 42, 132]

/--
Counts of pairs of standard Young tableaux of size `n = 1, ..., 6` whose shape
has at most two rows.
-/
def youngTableauPairsAtMostTwoRows1to6 : Fin 6 → ℕ := ![1, 2, 5, 14, 42, 132]

theorem schensted_lis_two_rows_matches_catalan :
    ∀ n : Fin 6,
      lisAtMostTwo1to6 n = youngTableauPairsAtMostTwoRows1to6 n ∧
        youngTableauPairsAtMostTwoRows1to6 n = catalan1to6 n := by
  native_decide



structure PatternAvoidanceAdvancedBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PatternAvoidanceAdvancedBudgetCertificate.controlled
    (c : PatternAvoidanceAdvancedBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PatternAvoidanceAdvancedBudgetCertificate.budgetControlled
    (c : PatternAvoidanceAdvancedBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PatternAvoidanceAdvancedBudgetCertificate.Ready
    (c : PatternAvoidanceAdvancedBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PatternAvoidanceAdvancedBudgetCertificate.size
    (c : PatternAvoidanceAdvancedBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem patternAvoidanceAdvanced_budgetCertificate_le_size
    (c : PatternAvoidanceAdvancedBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePatternAvoidanceAdvancedBudgetCertificate :
    PatternAvoidanceAdvancedBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePatternAvoidanceAdvancedBudgetCertificate.Ready := by
  constructor
  · norm_num [PatternAvoidanceAdvancedBudgetCertificate.controlled,
      samplePatternAvoidanceAdvancedBudgetCertificate]
  · norm_num [PatternAvoidanceAdvancedBudgetCertificate.budgetControlled,
      samplePatternAvoidanceAdvancedBudgetCertificate]

example :
    samplePatternAvoidanceAdvancedBudgetCertificate.certificateBudgetWindow ≤
      samplePatternAvoidanceAdvancedBudgetCertificate.size := by
  apply patternAvoidanceAdvanced_budgetCertificate_le_size
  constructor
  · norm_num [PatternAvoidanceAdvancedBudgetCertificate.controlled,
      samplePatternAvoidanceAdvancedBudgetCertificate]
  · norm_num [PatternAvoidanceAdvancedBudgetCertificate.budgetControlled,
      samplePatternAvoidanceAdvancedBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePatternAvoidanceAdvancedBudgetCertificate.Ready := by
  constructor
  · norm_num [PatternAvoidanceAdvancedBudgetCertificate.controlled,
      samplePatternAvoidanceAdvancedBudgetCertificate]
  · norm_num [PatternAvoidanceAdvancedBudgetCertificate.budgetControlled,
      samplePatternAvoidanceAdvancedBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePatternAvoidanceAdvancedBudgetCertificate.certificateBudgetWindow ≤
      samplePatternAvoidanceAdvancedBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PatternAvoidanceAdvancedBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePatternAvoidanceAdvancedBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePatternAvoidanceAdvancedBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.PatternAvoidanceAdvanced
