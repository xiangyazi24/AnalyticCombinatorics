import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Mellin Tauberian remainder schemas.

This module records finite bookkeeping for Mellin Tauberian remainders.
-/

namespace AnalyticCombinatorics.PartB.Ch5.MellinTauberianRemainderSchemas

structure MellinTauberianRemainderData where
  mellinStrip : ℕ
  remainderWindow : ℕ
  tauberianSlack : ℕ
deriving DecidableEq, Repr

def hasMellinStrip (d : MellinTauberianRemainderData) : Prop :=
  0 < d.mellinStrip

def remainderWindowControlled
    (d : MellinTauberianRemainderData) : Prop :=
  d.remainderWindow ≤ d.mellinStrip + d.tauberianSlack

def mellinTauberianRemainderReady
    (d : MellinTauberianRemainderData) : Prop :=
  hasMellinStrip d ∧ remainderWindowControlled d

def mellinTauberianRemainderBudget
    (d : MellinTauberianRemainderData) : ℕ :=
  d.mellinStrip + d.remainderWindow + d.tauberianSlack

theorem mellinTauberianRemainderReady.hasMellinStrip
    {d : MellinTauberianRemainderData}
    (h : mellinTauberianRemainderReady d) :
    hasMellinStrip d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget
    (d : MellinTauberianRemainderData) :
    d.remainderWindow ≤ mellinTauberianRemainderBudget d := by
  unfold mellinTauberianRemainderBudget
  omega

def sampleMellinTauberianRemainderData :
    MellinTauberianRemainderData :=
  { mellinStrip := 6, remainderWindow := 8, tauberianSlack := 3 }

example : mellinTauberianRemainderReady
    sampleMellinTauberianRemainderData := by
  norm_num [mellinTauberianRemainderReady, hasMellinStrip]
  norm_num [remainderWindowControlled, sampleMellinTauberianRemainderData]

example :
    mellinTauberianRemainderBudget sampleMellinTauberianRemainderData = 17 := by
  native_decide


structure MellinTauberianRemainderSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinTauberianRemainderSchemasBudgetCertificate.controlled
    (c : MellinTauberianRemainderSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MellinTauberianRemainderSchemasBudgetCertificate.budgetControlled
    (c : MellinTauberianRemainderSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MellinTauberianRemainderSchemasBudgetCertificate.Ready
    (c : MellinTauberianRemainderSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MellinTauberianRemainderSchemasBudgetCertificate.size
    (c : MellinTauberianRemainderSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem mellinTauberianRemainderSchemas_budgetCertificate_le_size
    (c : MellinTauberianRemainderSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMellinTauberianRemainderSchemasBudgetCertificate :
    MellinTauberianRemainderSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMellinTauberianRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinTauberianRemainderSchemasBudgetCertificate.controlled,
      sampleMellinTauberianRemainderSchemasBudgetCertificate]
  · norm_num [MellinTauberianRemainderSchemasBudgetCertificate.budgetControlled,
      sampleMellinTauberianRemainderSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMellinTauberianRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinTauberianRemainderSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMellinTauberianRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinTauberianRemainderSchemasBudgetCertificate.controlled,
      sampleMellinTauberianRemainderSchemasBudgetCertificate]
  · norm_num [MellinTauberianRemainderSchemasBudgetCertificate.budgetControlled,
      sampleMellinTauberianRemainderSchemasBudgetCertificate]

example :
    sampleMellinTauberianRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinTauberianRemainderSchemasBudgetCertificate.size := by
  apply mellinTauberianRemainderSchemas_budgetCertificate_le_size
  constructor
  · norm_num [MellinTauberianRemainderSchemasBudgetCertificate.controlled,
      sampleMellinTauberianRemainderSchemasBudgetCertificate]
  · norm_num [MellinTauberianRemainderSchemasBudgetCertificate.budgetControlled,
      sampleMellinTauberianRemainderSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List MellinTauberianRemainderSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMellinTauberianRemainderSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMellinTauberianRemainderSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.MellinTauberianRemainderSchemas

