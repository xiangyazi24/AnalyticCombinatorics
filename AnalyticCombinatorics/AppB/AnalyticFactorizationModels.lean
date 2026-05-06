import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic factorization models.

The schema tracks factor count, zero budget, and unit budget for finite
analytic factorization data.
-/

namespace AnalyticCombinatorics.AppB.AnalyticFactorizationModels

structure AnalyticFactorizationData where
  factorCount : ℕ
  zeroBudget : ℕ
  unitBudget : ℕ
deriving DecidableEq, Repr

def factorsNonempty (d : AnalyticFactorizationData) : Prop :=
  0 < d.factorCount

def zerosControlled (d : AnalyticFactorizationData) : Prop :=
  d.zeroBudget ≤ d.factorCount + d.unitBudget

def analyticFactorizationReady (d : AnalyticFactorizationData) : Prop :=
  factorsNonempty d ∧ zerosControlled d

def analyticFactorizationBudget (d : AnalyticFactorizationData) : ℕ :=
  d.factorCount + d.zeroBudget + d.unitBudget

theorem analyticFactorizationReady.factors {d : AnalyticFactorizationData}
    (h : analyticFactorizationReady d) :
    factorsNonempty d ∧ zerosControlled d ∧ d.zeroBudget ≤ analyticFactorizationBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticFactorizationBudget
  omega

theorem zeroBudget_le_factorizationBudget (d : AnalyticFactorizationData) :
    d.zeroBudget ≤ analyticFactorizationBudget d := by
  unfold analyticFactorizationBudget
  omega

def sampleAnalyticFactorizationData : AnalyticFactorizationData :=
  { factorCount := 4, zeroBudget := 9, unitBudget := 6 }

example : analyticFactorizationReady sampleAnalyticFactorizationData := by
  norm_num [analyticFactorizationReady, factorsNonempty]
  norm_num [zerosControlled, sampleAnalyticFactorizationData]

example : analyticFactorizationBudget sampleAnalyticFactorizationData = 19 := by
  native_decide

structure AnalyticFactorizationWindow where
  factorWindow : ℕ
  zeroWindow : ℕ
  unitWindow : ℕ
  factorizationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticFactorizationWindow.zerosControlled (w : AnalyticFactorizationWindow) : Prop :=
  w.zeroWindow ≤ w.factorWindow + w.unitWindow + w.slack

def analyticFactorizationWindowReady (w : AnalyticFactorizationWindow) : Prop :=
  0 < w.factorWindow ∧ w.zerosControlled ∧
    w.factorizationBudget ≤ w.factorWindow + w.zeroWindow + w.unitWindow + w.slack

def AnalyticFactorizationWindow.certificate (w : AnalyticFactorizationWindow) : ℕ :=
  w.factorWindow + w.zeroWindow + w.unitWindow + w.factorizationBudget + w.slack

theorem analyticFactorization_budget_le_certificate (w : AnalyticFactorizationWindow) :
    w.factorizationBudget ≤ w.certificate := by
  unfold AnalyticFactorizationWindow.certificate
  omega

def sampleAnalyticFactorizationWindow : AnalyticFactorizationWindow :=
  { factorWindow := 5, zeroWindow := 8, unitWindow := 4, factorizationBudget := 18, slack := 2 }

example : analyticFactorizationWindowReady sampleAnalyticFactorizationWindow := by
  norm_num [analyticFactorizationWindowReady, AnalyticFactorizationWindow.zerosControlled,
    sampleAnalyticFactorizationWindow]


structure AnalyticFactorizationModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticFactorizationModelsBudgetCertificate.controlled
    (c : AnalyticFactorizationModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticFactorizationModelsBudgetCertificate.budgetControlled
    (c : AnalyticFactorizationModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticFactorizationModelsBudgetCertificate.Ready
    (c : AnalyticFactorizationModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticFactorizationModelsBudgetCertificate.size
    (c : AnalyticFactorizationModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticFactorizationModels_budgetCertificate_le_size
    (c : AnalyticFactorizationModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticFactorizationModelsBudgetCertificate :
    AnalyticFactorizationModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticFactorizationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticFactorizationModelsBudgetCertificate.controlled,
      sampleAnalyticFactorizationModelsBudgetCertificate]
  · norm_num [AnalyticFactorizationModelsBudgetCertificate.budgetControlled,
      sampleAnalyticFactorizationModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticFactorizationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticFactorizationModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticFactorizationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticFactorizationModelsBudgetCertificate.controlled,
      sampleAnalyticFactorizationModelsBudgetCertificate]
  · norm_num [AnalyticFactorizationModelsBudgetCertificate.budgetControlled,
      sampleAnalyticFactorizationModelsBudgetCertificate]

example :
    sampleAnalyticFactorizationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticFactorizationModelsBudgetCertificate.size := by
  apply analyticFactorizationModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticFactorizationModelsBudgetCertificate.controlled,
      sampleAnalyticFactorizationModelsBudgetCertificate]
  · norm_num [AnalyticFactorizationModelsBudgetCertificate.budgetControlled,
      sampleAnalyticFactorizationModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticFactorizationModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticFactorizationModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticFactorizationModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticFactorizationModels
