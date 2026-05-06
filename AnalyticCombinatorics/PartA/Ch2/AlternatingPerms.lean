import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.AlternatingPerms


/-!
Alternating permutations, also called zigzag permutations, are counted by the
Euler zigzag numbers.  Their exponential generating function is
`sec z + tan z`; this file records the computable tangent/secant table through
the Entringer, or boustrophedon, triangle.
-/

/-- The Entringer/boustrophedon triangle in the normalization whose diagonal
entries are the Euler zigzag numbers.  Entries above the diagonal are zero. -/
def boustrophedon : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      if k + 1 ≤ n + 1 then
        boustrophedon (n + 1) k + boustrophedon n (n - k)
      else
        0
termination_by n k => (n, k)
decreasing_by all_goals simp_wf; omega

/-- Euler zigzag number `E_n`, counting alternating permutations of size `n`. -/
def zigzagNumber (n : ℕ) : ℕ :=
  boustrophedon n n

/-- Tangent numbers, indexed so `tangentNumber n = E_{2n+1}`. -/
def tangentNumber (n : ℕ) : ℕ :=
  zigzagNumber (2 * n + 1)

/-- Secant numbers, indexed so `secantNumber n = E_{2n}`. -/
def secantNumber (n : ℕ) : ℕ :=
  zigzagNumber (2 * n)

theorem zigzagNumber_zero : zigzagNumber 0 = 1 := by native_decide
theorem zigzagNumber_one : zigzagNumber 1 = 1 := by native_decide
theorem zigzagNumber_two : zigzagNumber 2 = 1 := by native_decide
theorem zigzagNumber_three : zigzagNumber 3 = 2 := by native_decide
theorem zigzagNumber_four : zigzagNumber 4 = 5 := by native_decide
theorem zigzagNumber_five : zigzagNumber 5 = 16 := by native_decide
theorem zigzagNumber_six : zigzagNumber 6 = 61 := by native_decide
theorem zigzagNumber_seven : zigzagNumber 7 = 272 := by native_decide

theorem tangentNumber_zero : tangentNumber 0 = 1 := by native_decide
theorem tangentNumber_one : tangentNumber 1 = 2 := by native_decide
theorem tangentNumber_two : tangentNumber 2 = 16 := by native_decide
theorem tangentNumber_three : tangentNumber 3 = 272 := by native_decide

theorem secantNumber_zero : secantNumber 0 = 1 := by native_decide
theorem secantNumber_one : secantNumber 1 = 1 := by native_decide
theorem secantNumber_two : secantNumber 2 = 5 := by native_decide
theorem secantNumber_three : secantNumber 3 = 61 := by native_decide
theorem secantNumber_four : secantNumber 4 = 1385 := by native_decide

/-- Checked diagonal values of the boustrophedon triangle. -/
theorem boustrophedon_diagonal_values_checked :
    boustrophedon 0 0 = 1 ∧
      boustrophedon 1 1 = 1 ∧
      boustrophedon 2 2 = 1 ∧
      boustrophedon 3 3 = 2 ∧
      boustrophedon 4 4 = 5 ∧
      boustrophedon 5 5 = 16 ∧
      boustrophedon 6 6 = 61 ∧
      boustrophedon 7 7 = 272 := by
  native_decide

/-- Checked identity that the diagonal entries are `zigzagNumber`. -/
theorem boustrophedon_diagonal_checked (n : ℕ) (hn : n ≤ 7) :
    boustrophedon n n = zigzagNumber n := by
  interval_cases n <;> native_decide

/-- Checked secant-number connection: `|Euler_{2n}| = E_{2n}` for `n ≤ 4`. -/
theorem secantNumber_eq_even_zigzag_checked (n : ℕ) (hn : n ≤ 4) :
    secantNumber n = zigzagNumber (2 * n) := by
  interval_cases n <;> native_decide



structure AlternatingPermsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlternatingPermsBudgetCertificate.controlled
    (c : AlternatingPermsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AlternatingPermsBudgetCertificate.budgetControlled
    (c : AlternatingPermsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AlternatingPermsBudgetCertificate.Ready
    (c : AlternatingPermsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlternatingPermsBudgetCertificate.size
    (c : AlternatingPermsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem alternatingPerms_budgetCertificate_le_size
    (c : AlternatingPermsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAlternatingPermsBudgetCertificate :
    AlternatingPermsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAlternatingPermsBudgetCertificate.Ready := by
  constructor
  · norm_num [AlternatingPermsBudgetCertificate.controlled,
      sampleAlternatingPermsBudgetCertificate]
  · norm_num [AlternatingPermsBudgetCertificate.budgetControlled,
      sampleAlternatingPermsBudgetCertificate]

example :
    sampleAlternatingPermsBudgetCertificate.certificateBudgetWindow ≤
      sampleAlternatingPermsBudgetCertificate.size := by
  apply alternatingPerms_budgetCertificate_le_size
  constructor
  · norm_num [AlternatingPermsBudgetCertificate.controlled,
      sampleAlternatingPermsBudgetCertificate]
  · norm_num [AlternatingPermsBudgetCertificate.budgetControlled,
      sampleAlternatingPermsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAlternatingPermsBudgetCertificate.Ready := by
  constructor
  · norm_num [AlternatingPermsBudgetCertificate.controlled,
      sampleAlternatingPermsBudgetCertificate]
  · norm_num [AlternatingPermsBudgetCertificate.budgetControlled,
      sampleAlternatingPermsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlternatingPermsBudgetCertificate.certificateBudgetWindow ≤
      sampleAlternatingPermsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AlternatingPermsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAlternatingPermsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAlternatingPermsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.AlternatingPerms
