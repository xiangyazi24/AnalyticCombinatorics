import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite sequence schema models.

The finite record stores sequence length, atom budget, and guard slack.
-/

namespace AnalyticCombinatorics.AppA.FiniteSequenceSchemaModels

structure SequenceSchemaData where
  sequenceLength : ℕ
  atomBudget : ℕ
  guardSlack : ℕ
deriving DecidableEq, Repr

def atomBudgetPositive (d : SequenceSchemaData) : Prop :=
  0 < d.atomBudget

def lengthControlled (d : SequenceSchemaData) : Prop :=
  d.sequenceLength ≤ d.atomBudget + d.guardSlack

def sequenceSchemaReady (d : SequenceSchemaData) : Prop :=
  atomBudgetPositive d ∧ lengthControlled d

def sequenceSchemaBudget (d : SequenceSchemaData) : ℕ :=
  d.sequenceLength + d.atomBudget + d.guardSlack

theorem sequenceSchemaReady.atoms {d : SequenceSchemaData}
    (h : sequenceSchemaReady d) :
    atomBudgetPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem sequenceLength_le_sequenceSchemaBudget
    (d : SequenceSchemaData) :
    d.sequenceLength ≤ sequenceSchemaBudget d := by
  unfold sequenceSchemaBudget
  omega

def sampleSequenceSchemaData : SequenceSchemaData :=
  { sequenceLength := 7, atomBudget := 5, guardSlack := 3 }

example : sequenceSchemaReady sampleSequenceSchemaData := by
  norm_num [sequenceSchemaReady, atomBudgetPositive]
  norm_num [lengthControlled, sampleSequenceSchemaData]

example : sequenceSchemaBudget sampleSequenceSchemaData = 15 := by
  native_decide

structure SequenceSchemaWindow where
  sequenceLength : ℕ
  atomBudget : ℕ
  guardSlack : ℕ
  constructionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SequenceSchemaWindow.lengthControlled (w : SequenceSchemaWindow) : Prop :=
  w.sequenceLength ≤ w.atomBudget + w.guardSlack + w.slack

def SequenceSchemaWindow.constructionControlled (w : SequenceSchemaWindow) : Prop :=
  w.constructionBudget ≤ w.sequenceLength + w.atomBudget + w.guardSlack + w.slack

def sequenceSchemaWindowReady (w : SequenceSchemaWindow) : Prop :=
  0 < w.atomBudget ∧
    w.lengthControlled ∧
    w.constructionControlled

def SequenceSchemaWindow.certificate (w : SequenceSchemaWindow) : ℕ :=
  w.sequenceLength + w.atomBudget + w.guardSlack + w.slack

theorem sequenceSchema_constructionBudget_le_certificate {w : SequenceSchemaWindow}
    (h : sequenceSchemaWindowReady w) :
    w.constructionBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hconstruction⟩
  exact hconstruction

def sampleSequenceSchemaWindow : SequenceSchemaWindow :=
  { sequenceLength := 7, atomBudget := 5, guardSlack := 3, constructionBudget := 14, slack := 0 }

example : sequenceSchemaWindowReady sampleSequenceSchemaWindow := by
  norm_num [sequenceSchemaWindowReady, SequenceSchemaWindow.lengthControlled,
    SequenceSchemaWindow.constructionControlled, sampleSequenceSchemaWindow]

example : sampleSequenceSchemaWindow.certificate = 15 := by
  native_decide


structure FiniteSequenceSchemaModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSequenceSchemaModelsBudgetCertificate.controlled
    (c : FiniteSequenceSchemaModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSequenceSchemaModelsBudgetCertificate.budgetControlled
    (c : FiniteSequenceSchemaModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSequenceSchemaModelsBudgetCertificate.Ready
    (c : FiniteSequenceSchemaModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSequenceSchemaModelsBudgetCertificate.size
    (c : FiniteSequenceSchemaModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSequenceSchemaModels_budgetCertificate_le_size
    (c : FiniteSequenceSchemaModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSequenceSchemaModelsBudgetCertificate :
    FiniteSequenceSchemaModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSequenceSchemaModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSequenceSchemaModelsBudgetCertificate.controlled,
      sampleFiniteSequenceSchemaModelsBudgetCertificate]
  · norm_num [FiniteSequenceSchemaModelsBudgetCertificate.budgetControlled,
      sampleFiniteSequenceSchemaModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSequenceSchemaModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSequenceSchemaModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSequenceSchemaModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSequenceSchemaModelsBudgetCertificate.controlled,
      sampleFiniteSequenceSchemaModelsBudgetCertificate]
  · norm_num [FiniteSequenceSchemaModelsBudgetCertificate.budgetControlled,
      sampleFiniteSequenceSchemaModelsBudgetCertificate]

example :
    sampleFiniteSequenceSchemaModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSequenceSchemaModelsBudgetCertificate.size := by
  apply finiteSequenceSchemaModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSequenceSchemaModelsBudgetCertificate.controlled,
      sampleFiniteSequenceSchemaModelsBudgetCertificate]
  · norm_num [FiniteSequenceSchemaModelsBudgetCertificate.budgetControlled,
      sampleFiniteSequenceSchemaModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteSequenceSchemaModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSequenceSchemaModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSequenceSchemaModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSequenceSchemaModels
