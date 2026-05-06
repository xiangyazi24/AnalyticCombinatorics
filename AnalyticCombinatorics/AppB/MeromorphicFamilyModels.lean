import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Meromorphic family models.

The finite schema stores parameter count, pole budget, and regularity
budget for meromorphic families.
-/

namespace AnalyticCombinatorics.AppB.MeromorphicFamilyModels

structure MeromorphicFamilyData where
  parameterCount : ℕ
  poleBudget : ℕ
  regularityBudget : ℕ
deriving DecidableEq, Repr

def parametersNonempty (d : MeromorphicFamilyData) : Prop :=
  0 < d.parameterCount

def polesControlled (d : MeromorphicFamilyData) : Prop :=
  d.poleBudget ≤ d.parameterCount + d.regularityBudget

def meromorphicFamilyReady (d : MeromorphicFamilyData) : Prop :=
  parametersNonempty d ∧ polesControlled d

def meromorphicFamilyBudget (d : MeromorphicFamilyData) : ℕ :=
  d.parameterCount + d.poleBudget + d.regularityBudget

theorem meromorphicFamilyReady.parameters {d : MeromorphicFamilyData}
    (h : meromorphicFamilyReady d) :
    parametersNonempty d ∧ polesControlled d ∧ d.poleBudget ≤ meromorphicFamilyBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold meromorphicFamilyBudget
  omega

theorem poleBudget_le_meromorphicBudget (d : MeromorphicFamilyData) :
    d.poleBudget ≤ meromorphicFamilyBudget d := by
  unfold meromorphicFamilyBudget
  omega

def sampleMeromorphicFamilyData : MeromorphicFamilyData :=
  { parameterCount := 5, poleBudget := 8, regularityBudget := 4 }

example : meromorphicFamilyReady sampleMeromorphicFamilyData := by
  norm_num [meromorphicFamilyReady, parametersNonempty]
  norm_num [polesControlled, sampleMeromorphicFamilyData]

example : meromorphicFamilyBudget sampleMeromorphicFamilyData = 17 := by
  native_decide

structure MeromorphicFamilyWindow where
  parameterWindow : ℕ
  poleWindow : ℕ
  regularityWindow : ℕ
  familyBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MeromorphicFamilyWindow.polesControlled (w : MeromorphicFamilyWindow) : Prop :=
  w.poleWindow ≤ w.parameterWindow + w.regularityWindow + w.slack

def meromorphicFamilyWindowReady (w : MeromorphicFamilyWindow) : Prop :=
  0 < w.parameterWindow ∧ w.polesControlled ∧
    w.familyBudget ≤ w.parameterWindow + w.poleWindow + w.regularityWindow + w.slack

def MeromorphicFamilyWindow.certificate (w : MeromorphicFamilyWindow) : ℕ :=
  w.parameterWindow + w.poleWindow + w.regularityWindow + w.familyBudget + w.slack

theorem meromorphicFamily_familyBudget_le_certificate (w : MeromorphicFamilyWindow) :
    w.familyBudget ≤ w.certificate := by
  unfold MeromorphicFamilyWindow.certificate
  omega

def sampleMeromorphicFamilyWindow : MeromorphicFamilyWindow :=
  { parameterWindow := 5, poleWindow := 8, regularityWindow := 4,
    familyBudget := 18, slack := 1 }

example : meromorphicFamilyWindowReady sampleMeromorphicFamilyWindow := by
  norm_num [meromorphicFamilyWindowReady, MeromorphicFamilyWindow.polesControlled,
    sampleMeromorphicFamilyWindow]


structure MeromorphicFamilyModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MeromorphicFamilyModelsBudgetCertificate.controlled
    (c : MeromorphicFamilyModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MeromorphicFamilyModelsBudgetCertificate.budgetControlled
    (c : MeromorphicFamilyModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MeromorphicFamilyModelsBudgetCertificate.Ready
    (c : MeromorphicFamilyModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MeromorphicFamilyModelsBudgetCertificate.size
    (c : MeromorphicFamilyModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem meromorphicFamilyModels_budgetCertificate_le_size
    (c : MeromorphicFamilyModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMeromorphicFamilyModelsBudgetCertificate :
    MeromorphicFamilyModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMeromorphicFamilyModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [MeromorphicFamilyModelsBudgetCertificate.controlled,
      sampleMeromorphicFamilyModelsBudgetCertificate]
  · norm_num [MeromorphicFamilyModelsBudgetCertificate.budgetControlled,
      sampleMeromorphicFamilyModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMeromorphicFamilyModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleMeromorphicFamilyModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMeromorphicFamilyModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [MeromorphicFamilyModelsBudgetCertificate.controlled,
      sampleMeromorphicFamilyModelsBudgetCertificate]
  · norm_num [MeromorphicFamilyModelsBudgetCertificate.budgetControlled,
      sampleMeromorphicFamilyModelsBudgetCertificate]

example :
    sampleMeromorphicFamilyModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleMeromorphicFamilyModelsBudgetCertificate.size := by
  apply meromorphicFamilyModels_budgetCertificate_le_size
  constructor
  · norm_num [MeromorphicFamilyModelsBudgetCertificate.controlled,
      sampleMeromorphicFamilyModelsBudgetCertificate]
  · norm_num [MeromorphicFamilyModelsBudgetCertificate.budgetControlled,
      sampleMeromorphicFamilyModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MeromorphicFamilyModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMeromorphicFamilyModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMeromorphicFamilyModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.MeromorphicFamilyModels
