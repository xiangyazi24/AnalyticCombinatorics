import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite species transport models.

The finite schema records source labels, target labels, and transport
slack for combinatorial species transfer data.
-/

namespace AnalyticCombinatorics.AppA.FiniteSpeciesTransportModels

structure SpeciesTransportData where
  sourceLabels : ℕ
  targetLabels : ℕ
  transportSlack : ℕ
deriving DecidableEq, Repr

def sourceLabelsNonempty (d : SpeciesTransportData) : Prop :=
  0 < d.sourceLabels

def targetsControlled (d : SpeciesTransportData) : Prop :=
  d.targetLabels ≤ d.sourceLabels + d.transportSlack

def speciesTransportReady (d : SpeciesTransportData) : Prop :=
  sourceLabelsNonempty d ∧ targetsControlled d

def speciesTransportBudget (d : SpeciesTransportData) : ℕ :=
  d.sourceLabels + d.targetLabels + d.transportSlack

theorem speciesTransportReady.source {d : SpeciesTransportData}
    (h : speciesTransportReady d) :
    sourceLabelsNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem targetLabels_le_speciesTransportBudget (d : SpeciesTransportData) :
    d.targetLabels ≤ speciesTransportBudget d := by
  unfold speciesTransportBudget
  omega

def sampleSpeciesTransportData : SpeciesTransportData :=
  { sourceLabels := 7, targetLabels := 9, transportSlack := 3 }

example : speciesTransportReady sampleSpeciesTransportData := by
  norm_num [speciesTransportReady, sourceLabelsNonempty]
  norm_num [targetsControlled, sampleSpeciesTransportData]

example : speciesTransportBudget sampleSpeciesTransportData = 19 := by
  native_decide

structure SpeciesTransportWindow where
  sourceLabels : ℕ
  targetLabels : ℕ
  transportSlack : ℕ
  relabelBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SpeciesTransportWindow.targetsControlled (w : SpeciesTransportWindow) : Prop :=
  w.targetLabels ≤ w.sourceLabels + w.transportSlack + w.slack

def SpeciesTransportWindow.relabelControlled (w : SpeciesTransportWindow) : Prop :=
  w.relabelBudget ≤ w.sourceLabels + w.targetLabels + w.transportSlack + w.slack

def speciesTransportWindowReady (w : SpeciesTransportWindow) : Prop :=
  0 < w.sourceLabels ∧
    w.targetsControlled ∧
    w.relabelControlled

def SpeciesTransportWindow.certificate (w : SpeciesTransportWindow) : ℕ :=
  w.sourceLabels + w.targetLabels + w.transportSlack + w.slack

theorem speciesTransport_relabelBudget_le_certificate {w : SpeciesTransportWindow}
    (h : speciesTransportWindowReady w) :
    w.relabelBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hrelabel⟩
  exact hrelabel

def sampleSpeciesTransportWindow : SpeciesTransportWindow :=
  { sourceLabels := 7, targetLabels := 9, transportSlack := 3, relabelBudget := 18, slack := 0 }

example : speciesTransportWindowReady sampleSpeciesTransportWindow := by
  norm_num [speciesTransportWindowReady, SpeciesTransportWindow.targetsControlled,
    SpeciesTransportWindow.relabelControlled, sampleSpeciesTransportWindow]

example : sampleSpeciesTransportWindow.certificate = 19 := by
  native_decide


structure FiniteSpeciesTransportModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSpeciesTransportModelsBudgetCertificate.controlled
    (c : FiniteSpeciesTransportModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSpeciesTransportModelsBudgetCertificate.budgetControlled
    (c : FiniteSpeciesTransportModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSpeciesTransportModelsBudgetCertificate.Ready
    (c : FiniteSpeciesTransportModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSpeciesTransportModelsBudgetCertificate.size
    (c : FiniteSpeciesTransportModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSpeciesTransportModels_budgetCertificate_le_size
    (c : FiniteSpeciesTransportModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSpeciesTransportModelsBudgetCertificate :
    FiniteSpeciesTransportModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSpeciesTransportModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesTransportModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesTransportModelsBudgetCertificate]
  · norm_num [FiniteSpeciesTransportModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesTransportModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSpeciesTransportModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesTransportModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSpeciesTransportModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesTransportModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesTransportModelsBudgetCertificate]
  · norm_num [FiniteSpeciesTransportModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesTransportModelsBudgetCertificate]

example :
    sampleFiniteSpeciesTransportModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesTransportModelsBudgetCertificate.size := by
  apply finiteSpeciesTransportModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSpeciesTransportModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesTransportModelsBudgetCertificate]
  · norm_num [FiniteSpeciesTransportModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesTransportModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteSpeciesTransportModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSpeciesTransportModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSpeciesTransportModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSpeciesTransportModels
