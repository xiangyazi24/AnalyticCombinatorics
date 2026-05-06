import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Mellin residue window schemas.

This module records finite bookkeeping for Mellin residue extraction.
-/

namespace AnalyticCombinatorics.PartB.Ch5.MellinResidueWindowSchemas

structure MellinResidueSchemaData where
  stripCount : ℕ
  residueWindow : ℕ
  mellinSlack : ℕ
deriving DecidableEq, Repr

def hasStripCount (d : MellinResidueSchemaData) : Prop :=
  0 < d.stripCount

def residueWindowControlled (d : MellinResidueSchemaData) : Prop :=
  d.residueWindow ≤ d.stripCount + d.mellinSlack

def mellinResidueSchemaReady (d : MellinResidueSchemaData) : Prop :=
  hasStripCount d ∧ residueWindowControlled d

def mellinResidueSchemaBudget (d : MellinResidueSchemaData) : ℕ :=
  d.stripCount + d.residueWindow + d.mellinSlack

theorem mellinResidueSchemaReady.hasStripCount
    {d : MellinResidueSchemaData}
    (h : mellinResidueSchemaReady d) :
    hasStripCount d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem residueWindow_le_budget (d : MellinResidueSchemaData) :
    d.residueWindow ≤ mellinResidueSchemaBudget d := by
  unfold mellinResidueSchemaBudget
  omega

def sampleMellinResidueSchemaData : MellinResidueSchemaData :=
  { stripCount := 6, residueWindow := 8, mellinSlack := 3 }

example : mellinResidueSchemaReady sampleMellinResidueSchemaData := by
  norm_num [mellinResidueSchemaReady, hasStripCount]
  norm_num [residueWindowControlled, sampleMellinResidueSchemaData]

example : mellinResidueSchemaBudget sampleMellinResidueSchemaData = 17 := by
  native_decide

structure MellinResidueWindowBudgetCertificate where
  stripWindow : ℕ
  residueWindow : ℕ
  mellinSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinResidueWindowBudgetCertificate.controlled
    (c : MellinResidueWindowBudgetCertificate) : Prop :=
  0 < c.stripWindow ∧
    c.residueWindow ≤ c.stripWindow + c.mellinSlackWindow + c.slack

def MellinResidueWindowBudgetCertificate.budgetControlled
    (c : MellinResidueWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.stripWindow + c.residueWindow + c.mellinSlackWindow + c.slack

def MellinResidueWindowBudgetCertificate.Ready
    (c : MellinResidueWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MellinResidueWindowBudgetCertificate.size
    (c : MellinResidueWindowBudgetCertificate) : ℕ :=
  c.stripWindow + c.residueWindow + c.mellinSlackWindow + c.slack

theorem mellinResidueWindow_budgetCertificate_le_size
    (c : MellinResidueWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMellinResidueWindowBudgetCertificate :
    MellinResidueWindowBudgetCertificate :=
  { stripWindow := 6
    residueWindow := 8
    mellinSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMellinResidueWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinResidueWindowBudgetCertificate.controlled,
      sampleMellinResidueWindowBudgetCertificate]
  · norm_num [MellinResidueWindowBudgetCertificate.budgetControlled,
      sampleMellinResidueWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMellinResidueWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinResidueWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMellinResidueWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinResidueWindowBudgetCertificate.controlled,
      sampleMellinResidueWindowBudgetCertificate]
  · norm_num [MellinResidueWindowBudgetCertificate.budgetControlled,
      sampleMellinResidueWindowBudgetCertificate]

example :
    sampleMellinResidueWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinResidueWindowBudgetCertificate.size := by
  apply mellinResidueWindow_budgetCertificate_le_size
  constructor
  · norm_num [MellinResidueWindowBudgetCertificate.controlled,
      sampleMellinResidueWindowBudgetCertificate]
  · norm_num [MellinResidueWindowBudgetCertificate.budgetControlled,
      sampleMellinResidueWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MellinResidueWindowBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleMellinResidueWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleMellinResidueWindowBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.MellinResidueWindowSchemas
