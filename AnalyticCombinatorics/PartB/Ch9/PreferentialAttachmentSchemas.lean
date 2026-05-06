import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Preferential attachment schema bookkeeping.

The finite data records attachment weight, initial mass, and variance
budget.
-/

namespace AnalyticCombinatorics.PartB.Ch9.PreferentialAttachmentSchemas

structure PreferentialAttachmentData where
  initialMass : ℕ
  attachmentWeight : ℕ
  varianceBudget : ℕ
deriving DecidableEq, Repr

def positiveInitialMass (d : PreferentialAttachmentData) : Prop :=
  0 < d.initialMass

def positiveAttachmentWeight (d : PreferentialAttachmentData) : Prop :=
  0 < d.attachmentWeight

def preferentialAttachmentReady (d : PreferentialAttachmentData) : Prop :=
  positiveInitialMass d ∧ positiveAttachmentWeight d

def attachmentBudget (d : PreferentialAttachmentData) : ℕ :=
  d.initialMass + d.attachmentWeight + d.varianceBudget

theorem preferentialAttachmentReady.weight {d : PreferentialAttachmentData}
    (h : preferentialAttachmentReady d) :
    positiveAttachmentWeight d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem initialMass_le_attachmentBudget (d : PreferentialAttachmentData) :
    d.initialMass ≤ attachmentBudget d := by
  unfold attachmentBudget
  omega

def samplePreferentialAttachment : PreferentialAttachmentData :=
  { initialMass := 5, attachmentWeight := 3, varianceBudget := 4 }

example : preferentialAttachmentReady samplePreferentialAttachment := by
  norm_num
    [preferentialAttachmentReady, positiveInitialMass, positiveAttachmentWeight,
      samplePreferentialAttachment]

example : attachmentBudget samplePreferentialAttachment = 12 := by
  native_decide

/-- Finite executable readiness audit for preferential-attachment data. -/
def preferentialAttachmentListReady
    (data : List PreferentialAttachmentData) : Bool :=
  data.all fun d =>
    0 < d.initialMass &&
      0 < d.attachmentWeight &&
        d.varianceBudget ≤ d.initialMass + d.attachmentWeight

theorem preferentialAttachmentList_readyWindow :
    preferentialAttachmentListReady
      [{ initialMass := 4, attachmentWeight := 2, varianceBudget := 3 },
       { initialMass := 5, attachmentWeight := 3, varianceBudget := 4 }] = true := by
  unfold preferentialAttachmentListReady
  native_decide

structure PreferentialAttachmentBudgetCertificate where
  initialMassWindow : ℕ
  attachmentWeightWindow : ℕ
  varianceBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PreferentialAttachmentBudgetCertificate.controlled
    (c : PreferentialAttachmentBudgetCertificate) : Prop :=
  0 < c.initialMassWindow ∧
    0 < c.attachmentWeightWindow ∧
      c.varianceBudgetWindow ≤
        c.initialMassWindow + c.attachmentWeightWindow + c.slack

def PreferentialAttachmentBudgetCertificate.budgetControlled
    (c : PreferentialAttachmentBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.initialMassWindow + c.attachmentWeightWindow + c.varianceBudgetWindow +
      c.slack

def PreferentialAttachmentBudgetCertificate.Ready
    (c : PreferentialAttachmentBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PreferentialAttachmentBudgetCertificate.size
    (c : PreferentialAttachmentBudgetCertificate) : ℕ :=
  c.initialMassWindow + c.attachmentWeightWindow + c.varianceBudgetWindow +
    c.slack

theorem preferentialAttachment_budgetCertificate_le_size
    (c : PreferentialAttachmentBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePreferentialAttachmentBudgetCertificate :
    PreferentialAttachmentBudgetCertificate :=
  { initialMassWindow := 5
    attachmentWeightWindow := 3
    varianceBudgetWindow := 4
    certificateBudgetWindow := 13
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePreferentialAttachmentBudgetCertificate.Ready := by
  constructor
  · norm_num [PreferentialAttachmentBudgetCertificate.controlled,
      samplePreferentialAttachmentBudgetCertificate]
  · norm_num [PreferentialAttachmentBudgetCertificate.budgetControlled,
      samplePreferentialAttachmentBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePreferentialAttachmentBudgetCertificate.certificateBudgetWindow ≤
      samplePreferentialAttachmentBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePreferentialAttachmentBudgetCertificate.Ready := by
  constructor
  · norm_num [PreferentialAttachmentBudgetCertificate.controlled,
      samplePreferentialAttachmentBudgetCertificate]
  · norm_num [PreferentialAttachmentBudgetCertificate.budgetControlled,
      samplePreferentialAttachmentBudgetCertificate]

example :
    samplePreferentialAttachmentBudgetCertificate.certificateBudgetWindow ≤
      samplePreferentialAttachmentBudgetCertificate.size := by
  apply preferentialAttachment_budgetCertificate_le_size
  constructor
  · norm_num [PreferentialAttachmentBudgetCertificate.controlled,
      samplePreferentialAttachmentBudgetCertificate]
  · norm_num [PreferentialAttachmentBudgetCertificate.budgetControlled,
      samplePreferentialAttachmentBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List PreferentialAttachmentBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePreferentialAttachmentBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    samplePreferentialAttachmentBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.PreferentialAttachmentSchemas
