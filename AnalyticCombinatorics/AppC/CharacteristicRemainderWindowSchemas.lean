import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Characteristic remainder window schemas.

This module records finite bookkeeping for characteristic-function remainders.
-/

namespace AnalyticCombinatorics.AppC.CharacteristicRemainderWindowSchemas

structure CharacteristicRemainderWindowData where
  frequencyScale : ℕ
  remainderWindow : ℕ
  frequencySlack : ℕ
deriving DecidableEq, Repr

def hasFrequencyScale (d : CharacteristicRemainderWindowData) : Prop :=
  0 < d.frequencyScale

def remainderWindowControlled
    (d : CharacteristicRemainderWindowData) : Prop :=
  d.remainderWindow ≤ d.frequencyScale + d.frequencySlack

def characteristicRemainderReady
    (d : CharacteristicRemainderWindowData) : Prop :=
  hasFrequencyScale d ∧ remainderWindowControlled d

def characteristicRemainderBudget
    (d : CharacteristicRemainderWindowData) : ℕ :=
  d.frequencyScale + d.remainderWindow + d.frequencySlack

theorem characteristicRemainderReady.hasFrequencyScale
    {d : CharacteristicRemainderWindowData}
    (h : characteristicRemainderReady d) :
    hasFrequencyScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget
    (d : CharacteristicRemainderWindowData) :
    d.remainderWindow ≤ characteristicRemainderBudget d := by
  unfold characteristicRemainderBudget
  omega

def sampleCharacteristicRemainderWindowData :
    CharacteristicRemainderWindowData :=
  { frequencyScale := 7, remainderWindow := 9, frequencySlack := 3 }

example : characteristicRemainderReady
    sampleCharacteristicRemainderWindowData := by
  norm_num [characteristicRemainderReady, hasFrequencyScale]
  norm_num [remainderWindowControlled, sampleCharacteristicRemainderWindowData]

example :
    characteristicRemainderBudget
      sampleCharacteristicRemainderWindowData = 19 := by
  native_decide

structure CharacteristicRemainderCertificateWindow where
  frequencyWindow : ℕ
  remainderWindow : ℕ
  frequencySlack : ℕ
  remainderBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CharacteristicRemainderCertificateWindow.remainderControlled
    (w : CharacteristicRemainderCertificateWindow) : Prop :=
  w.remainderWindow ≤ w.frequencyWindow + w.frequencySlack + w.slack

def characteristicRemainderCertificateReady
    (w : CharacteristicRemainderCertificateWindow) : Prop :=
  0 < w.frequencyWindow ∧ w.remainderControlled ∧
    w.remainderBudget ≤ w.frequencyWindow + w.remainderWindow + w.slack

def CharacteristicRemainderCertificateWindow.certificate
    (w : CharacteristicRemainderCertificateWindow) : ℕ :=
  w.frequencyWindow + w.remainderWindow + w.frequencySlack + w.remainderBudget + w.slack

theorem characteristicRemainder_budget_le_certificate
    (w : CharacteristicRemainderCertificateWindow) :
    w.remainderBudget ≤ w.certificate := by
  unfold CharacteristicRemainderCertificateWindow.certificate
  omega

def sampleCharacteristicRemainderCertificateWindow :
    CharacteristicRemainderCertificateWindow :=
  { frequencyWindow := 6, remainderWindow := 8, frequencySlack := 2,
    remainderBudget := 15, slack := 1 }

example : characteristicRemainderCertificateReady
    sampleCharacteristicRemainderCertificateWindow := by
  norm_num [characteristicRemainderCertificateReady,
    CharacteristicRemainderCertificateWindow.remainderControlled,
    sampleCharacteristicRemainderCertificateWindow]


structure CharacteristicRemainderWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CharacteristicRemainderWindowSchemasBudgetCertificate.controlled
    (c : CharacteristicRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CharacteristicRemainderWindowSchemasBudgetCertificate.budgetControlled
    (c : CharacteristicRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CharacteristicRemainderWindowSchemasBudgetCertificate.Ready
    (c : CharacteristicRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CharacteristicRemainderWindowSchemasBudgetCertificate.size
    (c : CharacteristicRemainderWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem characteristicRemainderWindowSchemas_budgetCertificate_le_size
    (c : CharacteristicRemainderWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCharacteristicRemainderWindowSchemasBudgetCertificate :
    CharacteristicRemainderWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCharacteristicRemainderWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CharacteristicRemainderWindowSchemasBudgetCertificate.controlled,
      sampleCharacteristicRemainderWindowSchemasBudgetCertificate]
  · norm_num [CharacteristicRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleCharacteristicRemainderWindowSchemasBudgetCertificate]

example : sampleCharacteristicRemainderWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CharacteristicRemainderWindowSchemasBudgetCertificate.controlled,
      sampleCharacteristicRemainderWindowSchemasBudgetCertificate]
  · norm_num [CharacteristicRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleCharacteristicRemainderWindowSchemasBudgetCertificate]

example :
    sampleCharacteristicRemainderWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCharacteristicRemainderWindowSchemasBudgetCertificate.size := by
  apply characteristicRemainderWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CharacteristicRemainderWindowSchemasBudgetCertificate.controlled,
      sampleCharacteristicRemainderWindowSchemasBudgetCertificate]
  · norm_num [CharacteristicRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleCharacteristicRemainderWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleCharacteristicRemainderWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCharacteristicRemainderWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CharacteristicRemainderWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCharacteristicRemainderWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCharacteristicRemainderWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.CharacteristicRemainderWindowSchemas
