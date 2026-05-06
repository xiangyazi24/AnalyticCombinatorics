import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite species transport window models.

This module records finite bookkeeping for species transport windows.
-/

namespace AnalyticCombinatorics.AppA.FiniteSpeciesTransportWindowModels

structure SpeciesTransportWindowData where
  sourceSpecies : ℕ
  transportWindow : ℕ
  transportSlack : ℕ
deriving DecidableEq, Repr

def hasSourceSpecies (d : SpeciesTransportWindowData) : Prop :=
  0 < d.sourceSpecies

def transportWindowControlled (d : SpeciesTransportWindowData) : Prop :=
  d.transportWindow ≤ d.sourceSpecies + d.transportSlack

def speciesTransportReady (d : SpeciesTransportWindowData) : Prop :=
  hasSourceSpecies d ∧ transportWindowControlled d

def speciesTransportBudget (d : SpeciesTransportWindowData) : ℕ :=
  d.sourceSpecies + d.transportWindow + d.transportSlack

theorem speciesTransportReady.hasSourceSpecies
    {d : SpeciesTransportWindowData}
    (h : speciesTransportReady d) :
    hasSourceSpecies d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem transportWindow_le_budget (d : SpeciesTransportWindowData) :
    d.transportWindow ≤ speciesTransportBudget d := by
  unfold speciesTransportBudget
  omega

def sampleSpeciesTransportWindowData : SpeciesTransportWindowData :=
  { sourceSpecies := 6, transportWindow := 8, transportSlack := 3 }

example : speciesTransportReady sampleSpeciesTransportWindowData := by
  norm_num [speciesTransportReady, hasSourceSpecies]
  norm_num [transportWindowControlled, sampleSpeciesTransportWindowData]

example : speciesTransportBudget sampleSpeciesTransportWindowData = 17 := by
  native_decide

structure SpeciesTransportCertificateWindow where
  sourceSpecies : ℕ
  transportWindow : ℕ
  transportSlack : ℕ
  relabelBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SpeciesTransportCertificateWindow.windowControlled
    (w : SpeciesTransportCertificateWindow) : Prop :=
  w.transportWindow ≤ w.sourceSpecies + w.transportSlack + w.slack

def SpeciesTransportCertificateWindow.relabelControlled
    (w : SpeciesTransportCertificateWindow) : Prop :=
  w.relabelBudget ≤ w.sourceSpecies + w.transportWindow + w.transportSlack + w.slack

def speciesTransportCertificateReady (w : SpeciesTransportCertificateWindow) : Prop :=
  0 < w.sourceSpecies ∧
    w.windowControlled ∧
    w.relabelControlled

def SpeciesTransportCertificateWindow.certificate
    (w : SpeciesTransportCertificateWindow) : ℕ :=
  w.sourceSpecies + w.transportWindow + w.transportSlack + w.slack

theorem speciesTransport_relabelBudget_le_certificate
    {w : SpeciesTransportCertificateWindow}
    (h : speciesTransportCertificateReady w) :
    w.relabelBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hrelabel⟩
  exact hrelabel

def sampleSpeciesTransportCertificateWindow : SpeciesTransportCertificateWindow :=
  { sourceSpecies := 6, transportWindow := 8, transportSlack := 3, relabelBudget := 16,
    slack := 0 }

example : speciesTransportCertificateReady sampleSpeciesTransportCertificateWindow := by
  norm_num [speciesTransportCertificateReady, SpeciesTransportCertificateWindow.windowControlled,
    SpeciesTransportCertificateWindow.relabelControlled, sampleSpeciesTransportCertificateWindow]

example : sampleSpeciesTransportCertificateWindow.certificate = 17 := by
  native_decide


structure FiniteSpeciesTransportWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSpeciesTransportWindowModelsBudgetCertificate.controlled
    (c : FiniteSpeciesTransportWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSpeciesTransportWindowModelsBudgetCertificate.budgetControlled
    (c : FiniteSpeciesTransportWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSpeciesTransportWindowModelsBudgetCertificate.Ready
    (c : FiniteSpeciesTransportWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSpeciesTransportWindowModelsBudgetCertificate.size
    (c : FiniteSpeciesTransportWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSpeciesTransportWindowModels_budgetCertificate_le_size
    (c : FiniteSpeciesTransportWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSpeciesTransportWindowModelsBudgetCertificate :
    FiniteSpeciesTransportWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSpeciesTransportWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesTransportWindowModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesTransportWindowModelsBudgetCertificate]
  · norm_num [FiniteSpeciesTransportWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesTransportWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSpeciesTransportWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesTransportWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSpeciesTransportWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesTransportWindowModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesTransportWindowModelsBudgetCertificate]
  · norm_num [FiniteSpeciesTransportWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesTransportWindowModelsBudgetCertificate]

example :
    sampleFiniteSpeciesTransportWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesTransportWindowModelsBudgetCertificate.size := by
  apply finiteSpeciesTransportWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSpeciesTransportWindowModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesTransportWindowModelsBudgetCertificate]
  · norm_num [FiniteSpeciesTransportWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesTransportWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteSpeciesTransportWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSpeciesTransportWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSpeciesTransportWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSpeciesTransportWindowModels
