import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Species transport window schemas.

This module records finite bookkeeping for transport windows in symbolic
constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.SpeciesTransportWindowSchemas

structure SpeciesTransportSchemaData where
  transportSites : ℕ
  labelWindow : ℕ
  transportSlack : ℕ
deriving DecidableEq, Repr

def hasTransportSites (d : SpeciesTransportSchemaData) : Prop :=
  0 < d.transportSites

def labelWindowControlled (d : SpeciesTransportSchemaData) : Prop :=
  d.labelWindow ≤ d.transportSites + d.transportSlack

def speciesTransportSchemaReady (d : SpeciesTransportSchemaData) : Prop :=
  hasTransportSites d ∧ labelWindowControlled d

def speciesTransportSchemaBudget (d : SpeciesTransportSchemaData) : ℕ :=
  d.transportSites + d.labelWindow + d.transportSlack

theorem speciesTransportSchemaReady.hasTransportSites
    {d : SpeciesTransportSchemaData}
    (h : speciesTransportSchemaReady d) :
    hasTransportSites d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem labelWindow_le_budget (d : SpeciesTransportSchemaData) :
    d.labelWindow ≤ speciesTransportSchemaBudget d := by
  unfold speciesTransportSchemaBudget
  omega

def sampleSpeciesTransportSchemaData : SpeciesTransportSchemaData :=
  { transportSites := 6, labelWindow := 8, transportSlack := 3 }

example : speciesTransportSchemaReady sampleSpeciesTransportSchemaData := by
  norm_num [speciesTransportSchemaReady, hasTransportSites]
  norm_num [labelWindowControlled, sampleSpeciesTransportSchemaData]

example : speciesTransportSchemaBudget sampleSpeciesTransportSchemaData = 17 := by
  native_decide

structure SpeciesTransportBudgetCertificate where
  transportSitesWindow : ℕ
  labelWindow : ℕ
  transportSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SpeciesTransportBudgetCertificate.controlled
    (c : SpeciesTransportBudgetCertificate) : Prop :=
  0 < c.transportSitesWindow ∧
    c.labelWindow ≤ c.transportSitesWindow + c.transportSlackWindow + c.slack

def SpeciesTransportBudgetCertificate.budgetControlled
    (c : SpeciesTransportBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.transportSitesWindow + c.labelWindow + c.transportSlackWindow + c.slack

def SpeciesTransportBudgetCertificate.Ready
    (c : SpeciesTransportBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SpeciesTransportBudgetCertificate.size
    (c : SpeciesTransportBudgetCertificate) : ℕ :=
  c.transportSitesWindow + c.labelWindow + c.transportSlackWindow + c.slack

theorem speciesTransport_budgetCertificate_le_size
    (c : SpeciesTransportBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSpeciesTransportBudgetCertificate :
    SpeciesTransportBudgetCertificate :=
  { transportSitesWindow := 6
    labelWindow := 8
    transportSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSpeciesTransportBudgetCertificate.Ready := by
  constructor
  · norm_num [SpeciesTransportBudgetCertificate.controlled,
      sampleSpeciesTransportBudgetCertificate]
  · norm_num [SpeciesTransportBudgetCertificate.budgetControlled,
      sampleSpeciesTransportBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSpeciesTransportBudgetCertificate.certificateBudgetWindow ≤
      sampleSpeciesTransportBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSpeciesTransportBudgetCertificate.Ready := by
  constructor
  · norm_num [SpeciesTransportBudgetCertificate.controlled,
      sampleSpeciesTransportBudgetCertificate]
  · norm_num [SpeciesTransportBudgetCertificate.budgetControlled,
      sampleSpeciesTransportBudgetCertificate]

example :
    sampleSpeciesTransportBudgetCertificate.certificateBudgetWindow ≤
      sampleSpeciesTransportBudgetCertificate.size := by
  apply speciesTransport_budgetCertificate_le_size
  constructor
  · norm_num [SpeciesTransportBudgetCertificate.controlled,
      sampleSpeciesTransportBudgetCertificate]
  · norm_num [SpeciesTransportBudgetCertificate.budgetControlled,
      sampleSpeciesTransportBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SpeciesTransportBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSpeciesTransportBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSpeciesTransportBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.SpeciesTransportWindowSchemas
