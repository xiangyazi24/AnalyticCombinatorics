import Mathlib.Tactic

namespace AnalyticCombinatorics.PartA.Ch1.WordPatterns

/-!
  Words over a binary alphabet avoiding short patterns.

  The count for words avoiding `000` is the tribonacci-type sequence obtained
  by splitting a valid word according to its final block: it ends in `1`, `01`,
  or `001`.  The count for monotone binary words has one choice of cut point.

  Binary words avoiding `11` are treated in
  `AnalyticCombinatorics.PartA.Ch1.StringsTheory`, where
  `stringsNoConsecOnes_count_succ_succ` gives the Fibonacci recurrence.
-/

set_option linter.style.show false
set_option linter.style.nativeDecide false

/-! ## Avoiding `000` -/

/-- Number of binary words of length `n` avoiding three consecutive zeros. -/
def noTripleZeroCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | n + 3 => noTripleZeroCount (n + 2) + noTripleZeroCount (n + 1) + noTripleZeroCount n

/-- Linear recurrence for words avoiding `000`. -/
theorem noTripleZeroCount_recurrence (n : ℕ) :
    noTripleZeroCount (n + 3) =
      noTripleZeroCount (n + 2) + noTripleZeroCount (n + 1) + noTripleZeroCount n := by
  rfl

theorem noTripleZeroCount_zero : noTripleZeroCount 0 = 1 := by native_decide
theorem noTripleZeroCount_one : noTripleZeroCount 1 = 2 := by native_decide
theorem noTripleZeroCount_two : noTripleZeroCount 2 = 4 := by native_decide
theorem noTripleZeroCount_three : noTripleZeroCount 3 = 7 := by native_decide
theorem noTripleZeroCount_four : noTripleZeroCount 4 = 13 := by native_decide
theorem noTripleZeroCount_five : noTripleZeroCount 5 = 24 := by native_decide
theorem noTripleZeroCount_six : noTripleZeroCount 6 = 44 := by native_decide

/-- A finite native check of the recurrence beyond the initial conditions. -/
theorem noTripleZeroCount_recurrence_check :
    noTripleZeroCount 3 = noTripleZeroCount 2 + noTripleZeroCount 1 + noTripleZeroCount 0 ∧
    noTripleZeroCount 4 = noTripleZeroCount 3 + noTripleZeroCount 2 + noTripleZeroCount 1 ∧
    noTripleZeroCount 5 = noTripleZeroCount 4 + noTripleZeroCount 3 + noTripleZeroCount 2 ∧
    noTripleZeroCount 6 = noTripleZeroCount 5 + noTripleZeroCount 4 + noTripleZeroCount 3 := by
  native_decide

/-! ## Monotone binary words -/

/--
Number of monotone binary words of length `n`.

There are `n + 1` choices for the cut point between the two constant blocks.
This is the same count for either orientation of the two blocks.
-/
def noZeroOneCount (n : ℕ) : ℕ :=
  n + 1

/-- Closed form for monotone binary words. -/
theorem noZeroOneCount_eq (n : ℕ) : noZeroOneCount n = n + 1 := by
  rfl

theorem noZeroOneCount_zero : noZeroOneCount 0 = 1 := by native_decide
theorem noZeroOneCount_one : noZeroOneCount 1 = 2 := by native_decide
theorem noZeroOneCount_two : noZeroOneCount 2 = 3 := by native_decide
theorem noZeroOneCount_three : noZeroOneCount 3 = 4 := by native_decide
theorem noZeroOneCount_four : noZeroOneCount 4 = 5 := by native_decide
theorem noZeroOneCount_five : noZeroOneCount 5 = 6 := by native_decide
theorem noZeroOneCount_six : noZeroOneCount 6 = 7 := by native_decide
theorem noZeroOneCount_seven : noZeroOneCount 7 = 8 := by native_decide
theorem noZeroOneCount_eight : noZeroOneCount 8 = 9 := by native_decide
theorem noZeroOneCount_nine : noZeroOneCount 9 = 10 := by native_decide
theorem noZeroOneCount_ten : noZeroOneCount 10 = 11 := by native_decide

/-- Native verification of the table for `n = 0, ..., 10`. -/
theorem noZeroOneCount_check_through_ten :
    noZeroOneCount 0 = 1 ∧
    noZeroOneCount 1 = 2 ∧
    noZeroOneCount 2 = 3 ∧
    noZeroOneCount 3 = 4 ∧
    noZeroOneCount 4 = 5 ∧
    noZeroOneCount 5 = 6 ∧
    noZeroOneCount 6 = 7 ∧
    noZeroOneCount 7 = 8 ∧
    noZeroOneCount 8 = 9 ∧
    noZeroOneCount 9 = 10 ∧
    noZeroOneCount 10 = 11 := by
  native_decide


structure WordPatternsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WordPatternsBudgetCertificate.controlled
    (c : WordPatternsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def WordPatternsBudgetCertificate.budgetControlled
    (c : WordPatternsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def WordPatternsBudgetCertificate.Ready
    (c : WordPatternsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WordPatternsBudgetCertificate.size
    (c : WordPatternsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem wordPatterns_budgetCertificate_le_size
    (c : WordPatternsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWordPatternsBudgetCertificate :
    WordPatternsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleWordPatternsBudgetCertificate.Ready := by
  constructor
  · norm_num [WordPatternsBudgetCertificate.controlled,
      sampleWordPatternsBudgetCertificate]
  · norm_num [WordPatternsBudgetCertificate.budgetControlled,
      sampleWordPatternsBudgetCertificate]

example :
    sampleWordPatternsBudgetCertificate.certificateBudgetWindow ≤
      sampleWordPatternsBudgetCertificate.size := by
  apply wordPatterns_budgetCertificate_le_size
  constructor
  · norm_num [WordPatternsBudgetCertificate.controlled,
      sampleWordPatternsBudgetCertificate]
  · norm_num [WordPatternsBudgetCertificate.budgetControlled,
      sampleWordPatternsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleWordPatternsBudgetCertificate.Ready := by
  constructor
  · norm_num [WordPatternsBudgetCertificate.controlled,
      sampleWordPatternsBudgetCertificate]
  · norm_num [WordPatternsBudgetCertificate.budgetControlled,
      sampleWordPatternsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWordPatternsBudgetCertificate.certificateBudgetWindow ≤
      sampleWordPatternsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List WordPatternsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleWordPatternsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleWordPatternsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.WordPatterns
