import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Continuous limit laws.
-/

namespace AnalyticCombinatorics.PartB.Ch9.ContinuousLimitLaws

/-- Finite grid density model for continuous limit-law approximations. -/
def uniformGridDensity (gridSize _ : ℕ) : ℚ :=
  1 / (gridSize + 1 : ℚ)

/-- Finite nonnegative density audit. -/
def densityNonnegativeUpTo (density : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun k => 0 ≤ density k

def densityPrefixQ (density : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl (fun total k => total + density k) 0

def ContinuousLawWindow (density : ℕ → ℚ) (N : ℕ) : Prop :=
  densityNonnegativeUpTo density N = true ∧ densityPrefixQ density N = 1

theorem uniformGrid_continuousWindow :
    ContinuousLawWindow (uniformGridDensity 7) 7 := by
  unfold ContinuousLawWindow densityNonnegativeUpTo densityPrefixQ
    uniformGridDensity
  native_decide

/-- First moment of a sampled density over a finite prefix. -/
def densityFirstMomentQ (density : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun (total : ℚ) (k : ℕ) => total + k * density k) 0

def FirstMomentWindow (density : ℕ → ℚ) (N : ℕ) (moment : ℚ) : Prop :=
  densityFirstMomentQ density N = moment

theorem uniformGrid_firstMomentWindow :
    FirstMomentWindow (uniformGridDensity 3) 3 (3 / 2) := by
  unfold FirstMomentWindow densityFirstMomentQ uniformGridDensity
  native_decide

example : uniformGridDensity 3 2 = 1 / 4 := by
  unfold uniformGridDensity
  native_decide

example : densityPrefixQ (uniformGridDensity 3) 3 = 1 := by
  unfold densityPrefixQ uniformGridDensity
  native_decide

structure ContinuousLimitLawsBudgetCertificate where
  densityWindow : ℕ
  transformWindow : ℕ
  convergenceWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ContinuousLimitLawsBudgetCertificate.controlled
    (c : ContinuousLimitLawsBudgetCertificate) : Prop :=
  0 < c.densityWindow ∧
    c.convergenceWindow ≤ c.densityWindow + c.transformWindow + c.slack

def ContinuousLimitLawsBudgetCertificate.budgetControlled
    (c : ContinuousLimitLawsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.densityWindow + c.transformWindow + c.convergenceWindow + c.slack

def ContinuousLimitLawsBudgetCertificate.Ready
    (c : ContinuousLimitLawsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ContinuousLimitLawsBudgetCertificate.size
    (c : ContinuousLimitLawsBudgetCertificate) : ℕ :=
  c.densityWindow + c.transformWindow + c.convergenceWindow + c.slack

theorem continuousLimitLaws_budgetCertificate_le_size
    (c : ContinuousLimitLawsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleContinuousLimitLawsBudgetCertificate :
    ContinuousLimitLawsBudgetCertificate :=
  { densityWindow := 5
    transformWindow := 6
    convergenceWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleContinuousLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [ContinuousLimitLawsBudgetCertificate.controlled,
      sampleContinuousLimitLawsBudgetCertificate]
  · norm_num [ContinuousLimitLawsBudgetCertificate.budgetControlled,
      sampleContinuousLimitLawsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleContinuousLimitLawsBudgetCertificate.certificateBudgetWindow ≤
      sampleContinuousLimitLawsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleContinuousLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [ContinuousLimitLawsBudgetCertificate.controlled,
      sampleContinuousLimitLawsBudgetCertificate]
  · norm_num [ContinuousLimitLawsBudgetCertificate.budgetControlled,
      sampleContinuousLimitLawsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ContinuousLimitLawsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleContinuousLimitLawsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleContinuousLimitLawsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.ContinuousLimitLaws
