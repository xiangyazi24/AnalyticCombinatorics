import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.Involutions


/-- Number of involutions on `n` labelled atoms. -/
def involutionCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => involutionCount (n + 1) + (n + 1) * involutionCount n

/-- Standalone form of the involution recurrence. -/
theorem involutionCount_rec (n : ℕ) :
    involutionCount (n + 2) =
      involutionCount (n + 1) + (n + 1) * involutionCount n := by
  rfl

theorem involutionCount_zero : involutionCount 0 = 1 := by
  native_decide

theorem involutionCount_one : involutionCount 1 = 1 := by
  native_decide

theorem involutionCount_two : involutionCount 2 = 2 := by
  native_decide

theorem involutionCount_three : involutionCount 3 = 4 := by
  native_decide

theorem involutionCount_four : involutionCount 4 = 10 := by
  native_decide

theorem involutionCount_five : involutionCount 5 = 26 := by
  native_decide

theorem involutionCount_six : involutionCount 6 = 76 := by
  native_decide

/-- The EGF coefficient stream `involutionCount n / n!`. -/
noncomputable def involutionEgfCoeff (n : ℕ) : ℚ :=
  (involutionCount n : ℚ) / n.factorial

/-- Coefficients of the formal series `exp(z + z^2 / 2)`. -/
noncomputable def expZAddZSquaredDivTwoCoeff (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n / 2 + 1),
    if 2 * j ≤ n then
      (1 : ℚ) / (((n - 2 * j).factorial * j.factorial * 2 ^ j : ℕ) : ℚ)
    else
      0

/-- EGF statement for involutions: `I(z) = exp(z + z^2 / 2)`. -/
def involutionEgf_eq_exp_z_add_z_squared_div_two : Prop :=
  involutionEgfCoeff = expZAddZSquaredDivTwoCoeff



structure InvolutionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def InvolutionsBudgetCertificate.controlled
    (c : InvolutionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def InvolutionsBudgetCertificate.budgetControlled
    (c : InvolutionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def InvolutionsBudgetCertificate.Ready
    (c : InvolutionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def InvolutionsBudgetCertificate.size
    (c : InvolutionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem involutions_budgetCertificate_le_size
    (c : InvolutionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleInvolutionsBudgetCertificate :
    InvolutionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleInvolutionsBudgetCertificate.Ready := by
  constructor
  · norm_num [InvolutionsBudgetCertificate.controlled,
      sampleInvolutionsBudgetCertificate]
  · norm_num [InvolutionsBudgetCertificate.budgetControlled,
      sampleInvolutionsBudgetCertificate]

example :
    sampleInvolutionsBudgetCertificate.certificateBudgetWindow ≤
      sampleInvolutionsBudgetCertificate.size := by
  apply involutions_budgetCertificate_le_size
  constructor
  · norm_num [InvolutionsBudgetCertificate.controlled,
      sampleInvolutionsBudgetCertificate]
  · norm_num [InvolutionsBudgetCertificate.budgetControlled,
      sampleInvolutionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleInvolutionsBudgetCertificate.Ready := by
  constructor
  · norm_num [InvolutionsBudgetCertificate.controlled,
      sampleInvolutionsBudgetCertificate]
  · norm_num [InvolutionsBudgetCertificate.budgetControlled,
      sampleInvolutionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleInvolutionsBudgetCertificate.certificateBudgetWindow ≤
      sampleInvolutionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List InvolutionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleInvolutionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleInvolutionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.Involutions
