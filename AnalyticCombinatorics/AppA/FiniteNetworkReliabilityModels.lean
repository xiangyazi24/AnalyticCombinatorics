import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite network reliability models.

The finite record stores component, path, and failure budgets for basic
reliability bookkeeping.
-/

namespace AnalyticCombinatorics.AppA.FiniteNetworkReliabilityModels

structure NetworkReliabilityData where
  components : ℕ
  workingPaths : ℕ
  failureBudget : ℕ
deriving DecidableEq, Repr

def componentNonempty (d : NetworkReliabilityData) : Prop :=
  0 < d.components

def pathsControlled (d : NetworkReliabilityData) : Prop :=
  d.workingPaths ≤ d.components + d.failureBudget

def networkReliabilityReady (d : NetworkReliabilityData) : Prop :=
  componentNonempty d ∧ pathsControlled d

def reliabilityBudget (d : NetworkReliabilityData) : ℕ :=
  d.components + d.workingPaths + d.failureBudget

theorem networkReliabilityReady.components {d : NetworkReliabilityData}
    (h : networkReliabilityReady d) :
    componentNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem workingPaths_le_reliabilityBudget (d : NetworkReliabilityData) :
    d.workingPaths ≤ reliabilityBudget d := by
  unfold reliabilityBudget
  omega

def sampleNetworkReliabilityData : NetworkReliabilityData :=
  { components := 9, workingPaths := 7, failureBudget := 3 }

example : networkReliabilityReady sampleNetworkReliabilityData := by
  norm_num [networkReliabilityReady, componentNonempty]
  norm_num [pathsControlled, sampleNetworkReliabilityData]

example : reliabilityBudget sampleNetworkReliabilityData = 19 := by
  native_decide

structure NetworkReliabilityWindow where
  components : ℕ
  workingPaths : ℕ
  failureBudget : ℕ
  reliabilityChecks : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def NetworkReliabilityWindow.pathsControlled (w : NetworkReliabilityWindow) : Prop :=
  w.workingPaths ≤ w.components + w.failureBudget + w.slack

def NetworkReliabilityWindow.checksControlled (w : NetworkReliabilityWindow) : Prop :=
  w.reliabilityChecks ≤ w.components + w.workingPaths + w.failureBudget + w.slack

def networkReliabilityWindowReady (w : NetworkReliabilityWindow) : Prop :=
  0 < w.components ∧
    w.pathsControlled ∧
    w.checksControlled

def NetworkReliabilityWindow.certificate (w : NetworkReliabilityWindow) : ℕ :=
  w.components + w.workingPaths + w.failureBudget + w.slack

theorem reliabilityChecks_le_certificate {w : NetworkReliabilityWindow}
    (h : networkReliabilityWindowReady w) :
    w.reliabilityChecks ≤ w.certificate := by
  rcases h with ⟨_, _, hchecks⟩
  exact hchecks

def sampleNetworkReliabilityWindow : NetworkReliabilityWindow :=
  { components := 9, workingPaths := 7, failureBudget := 3, reliabilityChecks := 18, slack := 0 }

example : networkReliabilityWindowReady sampleNetworkReliabilityWindow := by
  norm_num [networkReliabilityWindowReady, NetworkReliabilityWindow.pathsControlled,
    NetworkReliabilityWindow.checksControlled, sampleNetworkReliabilityWindow]

example : sampleNetworkReliabilityWindow.certificate = 19 := by
  native_decide


structure FiniteNetworkReliabilityModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteNetworkReliabilityModelsBudgetCertificate.controlled
    (c : FiniteNetworkReliabilityModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteNetworkReliabilityModelsBudgetCertificate.budgetControlled
    (c : FiniteNetworkReliabilityModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteNetworkReliabilityModelsBudgetCertificate.Ready
    (c : FiniteNetworkReliabilityModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteNetworkReliabilityModelsBudgetCertificate.size
    (c : FiniteNetworkReliabilityModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteNetworkReliabilityModels_budgetCertificate_le_size
    (c : FiniteNetworkReliabilityModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteNetworkReliabilityModelsBudgetCertificate :
    FiniteNetworkReliabilityModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteNetworkReliabilityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteNetworkReliabilityModelsBudgetCertificate.controlled,
      sampleFiniteNetworkReliabilityModelsBudgetCertificate]
  · norm_num [FiniteNetworkReliabilityModelsBudgetCertificate.budgetControlled,
      sampleFiniteNetworkReliabilityModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteNetworkReliabilityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteNetworkReliabilityModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteNetworkReliabilityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteNetworkReliabilityModelsBudgetCertificate.controlled,
      sampleFiniteNetworkReliabilityModelsBudgetCertificate]
  · norm_num [FiniteNetworkReliabilityModelsBudgetCertificate.budgetControlled,
      sampleFiniteNetworkReliabilityModelsBudgetCertificate]

example :
    sampleFiniteNetworkReliabilityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteNetworkReliabilityModelsBudgetCertificate.size := by
  apply finiteNetworkReliabilityModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteNetworkReliabilityModelsBudgetCertificate.controlled,
      sampleFiniteNetworkReliabilityModelsBudgetCertificate]
  · norm_num [FiniteNetworkReliabilityModelsBudgetCertificate.budgetControlled,
      sampleFiniteNetworkReliabilityModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteNetworkReliabilityModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteNetworkReliabilityModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteNetworkReliabilityModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteNetworkReliabilityModels
