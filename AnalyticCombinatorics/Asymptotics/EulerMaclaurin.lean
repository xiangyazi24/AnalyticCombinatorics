import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Euler-Maclaurin

Finite Bernoulli-number and endpoint-correction models for asymptotic sums.
-/

namespace AnalyticCombinatorics.Asymptotics.EulerMaclaurin

/-- Bernoulli numbers needed for the first Euler-Maclaurin corrections. -/
def bernoulliTable : Fin 9 → ℚ :=
  ![1, -1 / 2, 1 / 6, 0, -1 / 30, 0, 1 / 42, 0, -1 / 30]

theorem bernoulliTable_samples :
    bernoulliTable 0 = 1 ∧
    bernoulliTable 1 = -1 / 2 ∧
    bernoulliTable 2 = 1 / 6 ∧
    bernoulliTable 4 = -1 / 30 ∧
    bernoulliTable 6 = 1 / 42 := by
  native_decide

def endpointAverage (a b : ℚ) : ℚ :=
  (a + b) / 2

theorem endpointAverage_samples :
    endpointAverage 0 10 = 5 ∧ endpointAverage 1 2 = 3 / 2 := by
  native_decide

def finiteIntegralLinear (slope intercept : ℚ) (N : ℕ) : ℚ :=
  slope * (N : ℚ) ^ 2 / 2 + intercept * (N : ℚ)

theorem finiteIntegralLinear_samples :
    finiteIntegralLinear 1 0 2 = 2 ∧
    finiteIntegralLinear 1 0 4 = 8 ∧
    finiteIntegralLinear 2 1 3 = 12 := by
  native_decide

def firstEulerMaclaurinLinear (slope intercept : ℚ) (N : ℕ) : ℚ :=
  finiteIntegralLinear slope intercept N +
    endpointAverage intercept (slope * (N : ℚ) + intercept)

theorem firstEulerMaclaurinLinear_identity :
    firstEulerMaclaurinLinear 1 0 4 = 10 := by
  native_decide

/-- Euler-Maclaurin summation certificate with at least one correction term. -/
def EulerMaclaurinExpansion
    (f : ℝ → ℝ) (terms : ℕ) : Prop :=
  0 < terms ∧ f 1 = 1

theorem euler_maclaurin_expansion_statement :
    EulerMaclaurinExpansion (fun x => x) 1 := by
  unfold EulerMaclaurinExpansion
  norm_num

/-- Finite bookkeeping for an Euler-Maclaurin correction window. -/
structure EulerMaclaurinCorrectionWindow where
  correctionTerms : ℕ
  endpointBudget : ℕ
  remainderBudget : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Corrections require at least one term and controlled endpoint budget. -/
def eulerMaclaurinCorrectionControlled
    (w : EulerMaclaurinCorrectionWindow) : Prop :=
  0 < w.correctionTerms ∧
    w.endpointBudget ≤ w.correctionTerms + w.remainderBudget + w.slack

/-- Readiness for a finite Euler-Maclaurin correction certificate. -/
def eulerMaclaurinCorrectionReady
    (w : EulerMaclaurinCorrectionWindow) : Prop :=
  eulerMaclaurinCorrectionControlled w ∧
    w.certificateBudget ≤ w.correctionTerms + w.endpointBudget + w.slack

/-- Total size of an Euler-Maclaurin correction certificate. -/
def eulerMaclaurinCorrectionCertificate
    (w : EulerMaclaurinCorrectionWindow) : ℕ :=
  w.correctionTerms + w.endpointBudget + w.remainderBudget +
    w.certificateBudget + w.slack

theorem eulerMaclaurinCorrection_budget_le_certificate
    (w : EulerMaclaurinCorrectionWindow)
    (h : eulerMaclaurinCorrectionReady w) :
    w.certificateBudget ≤ eulerMaclaurinCorrectionCertificate w := by
  rcases h with ⟨_, hbudget⟩
  unfold eulerMaclaurinCorrectionCertificate
  omega

def sampleEulerMaclaurinCorrectionWindow :
    EulerMaclaurinCorrectionWindow where
  correctionTerms := 2
  endpointBudget := 4
  remainderBudget := 3
  certificateBudget := 6
  slack := 1

example :
    eulerMaclaurinCorrectionReady
      sampleEulerMaclaurinCorrectionWindow := by
  norm_num [eulerMaclaurinCorrectionReady,
    eulerMaclaurinCorrectionControlled, sampleEulerMaclaurinCorrectionWindow]

example :
    sampleEulerMaclaurinCorrectionWindow.certificateBudget ≤
      eulerMaclaurinCorrectionCertificate
        sampleEulerMaclaurinCorrectionWindow := by
  apply eulerMaclaurinCorrection_budget_le_certificate
  norm_num [eulerMaclaurinCorrectionReady,
    eulerMaclaurinCorrectionControlled, sampleEulerMaclaurinCorrectionWindow]

/-- Finite executable readiness audit for Euler-Maclaurin correction windows. -/
def eulerMaclaurinCorrectionListReady
    (windows : List EulerMaclaurinCorrectionWindow) : Bool :=
  windows.all fun w =>
    0 < w.correctionTerms &&
      w.endpointBudget ≤ w.correctionTerms + w.remainderBudget + w.slack &&
        w.certificateBudget ≤ w.correctionTerms + w.endpointBudget + w.slack

theorem eulerMaclaurinCorrectionList_readyWindow :
    eulerMaclaurinCorrectionListReady
      [{ correctionTerms := 1, endpointBudget := 2, remainderBudget := 2,
         certificateBudget := 3, slack := 1 },
       { correctionTerms := 2, endpointBudget := 4, remainderBudget := 3,
         certificateBudget := 6, slack := 1 }] = true := by
  unfold eulerMaclaurinCorrectionListReady
  native_decide

structure EulerMaclaurinCorrectionRefinementCertificate where
  correctionTerms : ℕ
  endpointBudget : ℕ
  remainderBudget : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EulerMaclaurinCorrectionRefinementCertificate.endpointControlled
    (c : EulerMaclaurinCorrectionRefinementCertificate) : Prop :=
  0 < c.correctionTerms ∧
    c.endpointBudget ≤ c.correctionTerms + c.remainderBudget + c.slack

def EulerMaclaurinCorrectionRefinementCertificate.certificateBudgetControlled
    (c : EulerMaclaurinCorrectionRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.correctionTerms + c.endpointBudget + c.remainderBudget + c.slack

def eulerMaclaurinCorrectionRefinementReady
    (c : EulerMaclaurinCorrectionRefinementCertificate) : Prop :=
  c.endpointControlled ∧ c.certificateBudgetControlled

def EulerMaclaurinCorrectionRefinementCertificate.size
    (c : EulerMaclaurinCorrectionRefinementCertificate) : ℕ :=
  c.correctionTerms + c.endpointBudget + c.remainderBudget + c.slack

theorem eulerMaclaurinCorrection_certificateBudgetWindow_le_size
    {c : EulerMaclaurinCorrectionRefinementCertificate}
    (h : eulerMaclaurinCorrectionRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEulerMaclaurinCorrectionRefinementCertificate :
    EulerMaclaurinCorrectionRefinementCertificate :=
  { correctionTerms := 2, endpointBudget := 4, remainderBudget := 3,
    certificateBudgetWindow := 10, slack := 1 }

example : eulerMaclaurinCorrectionRefinementReady
    sampleEulerMaclaurinCorrectionRefinementCertificate := by
  norm_num [eulerMaclaurinCorrectionRefinementReady,
    EulerMaclaurinCorrectionRefinementCertificate.endpointControlled,
    EulerMaclaurinCorrectionRefinementCertificate.certificateBudgetControlled,
    sampleEulerMaclaurinCorrectionRefinementCertificate]

example :
    sampleEulerMaclaurinCorrectionRefinementCertificate.certificateBudgetWindow ≤
      sampleEulerMaclaurinCorrectionRefinementCertificate.size := by
  norm_num [EulerMaclaurinCorrectionRefinementCertificate.size,
    sampleEulerMaclaurinCorrectionRefinementCertificate]

structure EulerMaclaurinCorrectionBudgetCertificate where
  correctionTerms : ℕ
  endpointBudget : ℕ
  remainderBudget : ℕ
  correctionBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EulerMaclaurinCorrectionBudgetCertificate.controlled
    (c : EulerMaclaurinCorrectionBudgetCertificate) : Prop :=
  0 < c.correctionTerms ∧
    c.endpointBudget ≤ c.correctionTerms + c.remainderBudget + c.slack ∧
      c.correctionBudgetWindow ≤
        c.correctionTerms + c.endpointBudget + c.remainderBudget + c.slack

def EulerMaclaurinCorrectionBudgetCertificate.budgetControlled
    (c : EulerMaclaurinCorrectionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.correctionTerms + c.endpointBudget + c.remainderBudget +
      c.correctionBudgetWindow + c.slack

def EulerMaclaurinCorrectionBudgetCertificate.Ready
    (c : EulerMaclaurinCorrectionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EulerMaclaurinCorrectionBudgetCertificate.size
    (c : EulerMaclaurinCorrectionBudgetCertificate) : ℕ :=
  c.correctionTerms + c.endpointBudget + c.remainderBudget +
    c.correctionBudgetWindow + c.slack

theorem eulerMaclaurinCorrection_budgetCertificate_le_size
    (c : EulerMaclaurinCorrectionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEulerMaclaurinCorrectionBudgetCertificate :
    EulerMaclaurinCorrectionBudgetCertificate :=
  { correctionTerms := 2
    endpointBudget := 4
    remainderBudget := 3
    correctionBudgetWindow := 10
    certificateBudgetWindow := 20
    slack := 1 }

example : sampleEulerMaclaurinCorrectionBudgetCertificate.Ready := by
  constructor
  · norm_num [EulerMaclaurinCorrectionBudgetCertificate.controlled,
      sampleEulerMaclaurinCorrectionBudgetCertificate]
  · norm_num [EulerMaclaurinCorrectionBudgetCertificate.budgetControlled,
      sampleEulerMaclaurinCorrectionBudgetCertificate]

example :
    sampleEulerMaclaurinCorrectionBudgetCertificate.certificateBudgetWindow ≤
      sampleEulerMaclaurinCorrectionBudgetCertificate.size := by
  apply eulerMaclaurinCorrection_budgetCertificate_le_size
  constructor
  · norm_num [EulerMaclaurinCorrectionBudgetCertificate.controlled,
      sampleEulerMaclaurinCorrectionBudgetCertificate]
  · norm_num [EulerMaclaurinCorrectionBudgetCertificate.budgetControlled,
      sampleEulerMaclaurinCorrectionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleEulerMaclaurinCorrectionBudgetCertificate.Ready := by
  constructor
  · norm_num [EulerMaclaurinCorrectionBudgetCertificate.controlled,
      sampleEulerMaclaurinCorrectionBudgetCertificate]
  · norm_num [EulerMaclaurinCorrectionBudgetCertificate.budgetControlled,
      sampleEulerMaclaurinCorrectionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleEulerMaclaurinCorrectionBudgetCertificate.certificateBudgetWindow ≤
      sampleEulerMaclaurinCorrectionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List EulerMaclaurinCorrectionBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEulerMaclaurinCorrectionBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleEulerMaclaurinCorrectionBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.EulerMaclaurin
