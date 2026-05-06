import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic sector cover models.

The finite abstraction records sector count, aperture budget, and overlap
slack.
-/

namespace AnalyticCombinatorics.AppB.AnalyticSectorCoverModels

structure AnalyticSectorCoverData where
  sectorCount : ℕ
  apertureBudget : ℕ
  overlapSlack : ℕ
deriving DecidableEq, Repr

def sectorCountPositive (d : AnalyticSectorCoverData) : Prop :=
  0 < d.sectorCount

def apertureControlled (d : AnalyticSectorCoverData) : Prop :=
  d.apertureBudget ≤ d.sectorCount + d.overlapSlack

def analyticSectorCoverReady (d : AnalyticSectorCoverData) : Prop :=
  sectorCountPositive d ∧ apertureControlled d

def analyticSectorCoverBudget (d : AnalyticSectorCoverData) : ℕ :=
  d.sectorCount + d.apertureBudget + d.overlapSlack

theorem analyticSectorCoverReady.sectors {d : AnalyticSectorCoverData}
    (h : analyticSectorCoverReady d) :
    sectorCountPositive d ∧ apertureControlled d ∧
      d.apertureBudget ≤ analyticSectorCoverBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticSectorCoverBudget
  omega

theorem apertureBudget_le_sectorCoverBudget
    (d : AnalyticSectorCoverData) :
    d.apertureBudget ≤ analyticSectorCoverBudget d := by
  unfold analyticSectorCoverBudget
  omega

def sampleAnalyticSectorCoverData : AnalyticSectorCoverData :=
  { sectorCount := 5, apertureBudget := 7, overlapSlack := 3 }

example : analyticSectorCoverReady sampleAnalyticSectorCoverData := by
  norm_num [analyticSectorCoverReady, sectorCountPositive]
  norm_num [apertureControlled, sampleAnalyticSectorCoverData]

example : analyticSectorCoverBudget sampleAnalyticSectorCoverData = 15 := by
  native_decide


structure AnalyticSectorCoverModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticSectorCoverModelsBudgetCertificate.controlled
    (c : AnalyticSectorCoverModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticSectorCoverModelsBudgetCertificate.budgetControlled
    (c : AnalyticSectorCoverModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticSectorCoverModelsBudgetCertificate.Ready
    (c : AnalyticSectorCoverModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticSectorCoverModelsBudgetCertificate.size
    (c : AnalyticSectorCoverModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticSectorCoverModels_budgetCertificate_le_size
    (c : AnalyticSectorCoverModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticSectorCoverModelsBudgetCertificate :
    AnalyticSectorCoverModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticSectorCoverModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticSectorCoverModelsBudgetCertificate.controlled,
      sampleAnalyticSectorCoverModelsBudgetCertificate]
  · norm_num [AnalyticSectorCoverModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSectorCoverModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticSectorCoverModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticSectorCoverModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticSectorCoverModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticSectorCoverModelsBudgetCertificate.controlled,
      sampleAnalyticSectorCoverModelsBudgetCertificate]
  · norm_num [AnalyticSectorCoverModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSectorCoverModelsBudgetCertificate]

example :
    sampleAnalyticSectorCoverModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticSectorCoverModelsBudgetCertificate.size := by
  apply analyticSectorCoverModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticSectorCoverModelsBudgetCertificate.controlled,
      sampleAnalyticSectorCoverModelsBudgetCertificate]
  · norm_num [AnalyticSectorCoverModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSectorCoverModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticSectorCoverModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticSectorCoverModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticSectorCoverModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticSectorCoverModels
