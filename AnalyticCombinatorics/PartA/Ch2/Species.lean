import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Species bookkeeping schemas.
-/

namespace AnalyticCombinatorics.PartA.Ch2.Species

structure SpeciesData where
  labelSetSize : ℕ
  transportCount : ℕ
  speciesSlack : ℕ
deriving DecidableEq, Repr

def speciesReady (d : SpeciesData) : Prop :=
  0 < d.labelSetSize ∧ d.transportCount ≤ d.labelSetSize + d.speciesSlack

def speciesBudget (d : SpeciesData) : ℕ :=
  d.labelSetSize + d.transportCount + d.speciesSlack

theorem transportCount_le_budget (d : SpeciesData) :
    d.transportCount ≤ speciesBudget d := by
  unfold speciesBudget
  omega

def sampleSpeciesData : SpeciesData :=
  { labelSetSize := 5, transportCount := 7, speciesSlack := 2 }

example : speciesReady sampleSpeciesData := by
  norm_num [speciesReady, sampleSpeciesData]

example : speciesBudget sampleSpeciesData = 14 := by native_decide

structure SpeciesTransportWindow where
  labelSetSize : ℕ
  relabellings : ℕ
  fixedStructures : ℕ
  transportSlack : ℕ
deriving DecidableEq, Repr

def SpeciesTransportWindow.relabellingBudget (w : SpeciesTransportWindow) : ℕ :=
  w.labelSetSize.factorial + w.transportSlack

def SpeciesTransportWindow.ready (w : SpeciesTransportWindow) : Prop :=
  w.relabellings ≤ w.relabellingBudget ∧ w.fixedStructures ≤ w.relabellings + w.transportSlack

def SpeciesTransportWindow.certificate (w : SpeciesTransportWindow) : ℕ :=
  w.labelSetSize + w.relabellings + w.fixedStructures + w.transportSlack

theorem fixedStructures_le_certificate (w : SpeciesTransportWindow) :
    w.fixedStructures ≤ w.certificate := by
  unfold SpeciesTransportWindow.certificate
  omega

def sampleSpeciesTransportWindow : SpeciesTransportWindow :=
  { labelSetSize := 4, relabellings := 24, fixedStructures := 6, transportSlack := 0 }

example : sampleSpeciesTransportWindow.ready := by
  norm_num [sampleSpeciesTransportWindow, SpeciesTransportWindow.ready,
    SpeciesTransportWindow.relabellingBudget]

example : sampleSpeciesTransportWindow.certificate = 34 := by
  native_decide


structure SpeciesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SpeciesBudgetCertificate.controlled
    (c : SpeciesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SpeciesBudgetCertificate.budgetControlled
    (c : SpeciesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SpeciesBudgetCertificate.Ready
    (c : SpeciesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SpeciesBudgetCertificate.size
    (c : SpeciesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem species_budgetCertificate_le_size
    (c : SpeciesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSpeciesBudgetCertificate :
    SpeciesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSpeciesBudgetCertificate.Ready := by
  constructor
  · norm_num [SpeciesBudgetCertificate.controlled,
      sampleSpeciesBudgetCertificate]
  · norm_num [SpeciesBudgetCertificate.budgetControlled,
      sampleSpeciesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSpeciesBudgetCertificate.certificateBudgetWindow ≤
      sampleSpeciesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSpeciesBudgetCertificate.Ready := by
  constructor
  · norm_num [SpeciesBudgetCertificate.controlled,
      sampleSpeciesBudgetCertificate]
  · norm_num [SpeciesBudgetCertificate.budgetControlled,
      sampleSpeciesBudgetCertificate]

example :
    sampleSpeciesBudgetCertificate.certificateBudgetWindow ≤
      sampleSpeciesBudgetCertificate.size := by
  apply species_budgetCertificate_le_size
  constructor
  · norm_num [SpeciesBudgetCertificate.controlled,
      sampleSpeciesBudgetCertificate]
  · norm_num [SpeciesBudgetCertificate.budgetControlled,
      sampleSpeciesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SpeciesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSpeciesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSpeciesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.Species
