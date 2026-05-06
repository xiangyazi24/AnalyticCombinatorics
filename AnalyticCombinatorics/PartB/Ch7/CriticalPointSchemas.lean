import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Critical point schemas.

The finite data records critical multiplicity, neighborhood radius, and
perturbation budget.
-/

namespace AnalyticCombinatorics.PartB.Ch7.CriticalPointSchemas

structure CriticalPointData where
  multiplicity : ℕ
  neighborhoodRadius : ℕ
  perturbationBudget : ℕ
deriving DecidableEq, Repr

def multiplicityPositive (d : CriticalPointData) : Prop :=
  0 < d.multiplicity

def radiusControlled (d : CriticalPointData) : Prop :=
  d.neighborhoodRadius ≤ d.multiplicity + d.perturbationBudget

def criticalPointReady (d : CriticalPointData) : Prop :=
  multiplicityPositive d ∧ radiusControlled d

def criticalPointBudget (d : CriticalPointData) : ℕ :=
  d.multiplicity + d.neighborhoodRadius + d.perturbationBudget

theorem criticalPointReady.multiplicity {d : CriticalPointData}
    (h : criticalPointReady d) :
    multiplicityPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem radius_le_criticalPointBudget (d : CriticalPointData) :
    d.neighborhoodRadius ≤ criticalPointBudget d := by
  unfold criticalPointBudget
  omega

def sampleCriticalPointData : CriticalPointData :=
  { multiplicity := 3, neighborhoodRadius := 7, perturbationBudget := 5 }

example : criticalPointReady sampleCriticalPointData := by
  norm_num [criticalPointReady, multiplicityPositive]
  norm_num [radiusControlled, sampleCriticalPointData]

example : criticalPointBudget sampleCriticalPointData = 15 := by
  native_decide

structure CriticalPointWindow where
  multiplicity : ℕ
  neighborhoodRadius : ℕ
  perturbationBudget : ℕ
  localNormalBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CriticalPointWindow.radiusControlled (w : CriticalPointWindow) : Prop :=
  w.neighborhoodRadius ≤ w.multiplicity + w.perturbationBudget + w.slack

def CriticalPointWindow.normalControlled (w : CriticalPointWindow) : Prop :=
  w.localNormalBudget ≤ w.multiplicity + w.neighborhoodRadius + w.perturbationBudget + w.slack

def criticalPointWindowReady (w : CriticalPointWindow) : Prop :=
  0 < w.multiplicity ∧
    w.radiusControlled ∧
    w.normalControlled

def CriticalPointWindow.certificate (w : CriticalPointWindow) : ℕ :=
  w.multiplicity + w.neighborhoodRadius + w.perturbationBudget + w.slack

theorem criticalPoint_localNormalBudget_le_certificate {w : CriticalPointWindow}
    (h : criticalPointWindowReady w) :
    w.localNormalBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hnormal⟩
  exact hnormal

def sampleCriticalPointWindow : CriticalPointWindow :=
  { multiplicity := 3, neighborhoodRadius := 7, perturbationBudget := 5, localNormalBudget := 14,
    slack := 0 }

example : criticalPointWindowReady sampleCriticalPointWindow := by
  norm_num [criticalPointWindowReady, CriticalPointWindow.radiusControlled,
    CriticalPointWindow.normalControlled, sampleCriticalPointWindow]

example : sampleCriticalPointWindow.certificate = 15 := by
  native_decide


structure CriticalPointSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CriticalPointSchemasBudgetCertificate.controlled
    (c : CriticalPointSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CriticalPointSchemasBudgetCertificate.budgetControlled
    (c : CriticalPointSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CriticalPointSchemasBudgetCertificate.Ready
    (c : CriticalPointSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CriticalPointSchemasBudgetCertificate.size
    (c : CriticalPointSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem criticalPointSchemas_budgetCertificate_le_size
    (c : CriticalPointSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCriticalPointSchemasBudgetCertificate :
    CriticalPointSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCriticalPointSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CriticalPointSchemasBudgetCertificate.controlled,
      sampleCriticalPointSchemasBudgetCertificate]
  · norm_num [CriticalPointSchemasBudgetCertificate.budgetControlled,
      sampleCriticalPointSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCriticalPointSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalPointSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCriticalPointSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CriticalPointSchemasBudgetCertificate.controlled,
      sampleCriticalPointSchemasBudgetCertificate]
  · norm_num [CriticalPointSchemasBudgetCertificate.budgetControlled,
      sampleCriticalPointSchemasBudgetCertificate]

example :
    sampleCriticalPointSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalPointSchemasBudgetCertificate.size := by
  apply criticalPointSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CriticalPointSchemasBudgetCertificate.controlled,
      sampleCriticalPointSchemasBudgetCertificate]
  · norm_num [CriticalPointSchemasBudgetCertificate.budgetControlled,
      sampleCriticalPointSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CriticalPointSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCriticalPointSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCriticalPointSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.CriticalPointSchemas
