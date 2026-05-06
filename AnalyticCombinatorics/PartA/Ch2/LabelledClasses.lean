import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Labelled classes and exponential generating functions.

Finite label-set and EGF coefficient-window bookkeeping.
-/

namespace AnalyticCombinatorics.PartA.Ch2.LabelledClasses

/-- EGF numerator convention: labelled objects multiplied by `n!`. -/
def egfNumerator (objects n : ℕ) : ℕ :=
  objects * n.factorial

/-- Singleton labelled class: exactly one structure on each singleton label set. -/
def singletonLabelledClass : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | _ => 0

/-- Finite audit that labelled counts fit inside all labellings. -/
def labelledClassEnvelopeCheck (objects : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => objects n ≤ n.factorial

def LabelledClassEGFWindow (objects : ℕ → ℕ) (N : ℕ) : Prop :=
  labelledClassEnvelopeCheck objects N = true

theorem singletonLabelledClass_egfNumerator_samples :
    egfNumerator (singletonLabelledClass 1) 1 = 1 ∧
    egfNumerator (singletonLabelledClass 2) 2 = 0 := by
  unfold egfNumerator singletonLabelledClass
  native_decide

theorem singletonLabelledClass_window :
    LabelledClassEGFWindow singletonLabelledClass 8 := by
  unfold LabelledClassEGFWindow labelledClassEnvelopeCheck
    singletonLabelledClass
  native_decide

structure LabelledClassWindow where
  labelCount : ℕ
  structureCount : ℕ
  egfDepth : ℕ
  labelSlack : ℕ
deriving DecidableEq, Repr

def labelledClassWindowReady (w : LabelledClassWindow) : Prop :=
  0 < w.labelCount ∧
    w.egfDepth ≤ w.labelCount + w.structureCount + w.labelSlack

def labelledClassWindowBudget (w : LabelledClassWindow) : ℕ :=
  w.labelCount + w.structureCount + w.egfDepth + w.labelSlack

theorem egfDepth_le_budget (w : LabelledClassWindow) :
    w.egfDepth ≤ labelledClassWindowBudget w := by
  unfold labelledClassWindowBudget
  omega

def sampleLabelledClassWindow : LabelledClassWindow :=
  { labelCount := 6, structureCount := 4, egfDepth := 8, labelSlack := 1 }

example : labelledClassWindowReady sampleLabelledClassWindow := by
  norm_num [labelledClassWindowReady, sampleLabelledClassWindow]

structure LabelledClassesBudgetCertificate where
  labelWindow : ℕ
  structureWindow : ℕ
  egfWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledClassesBudgetCertificate.controlled
    (c : LabelledClassesBudgetCertificate) : Prop :=
  0 < c.labelWindow ∧ c.egfWindow ≤ c.labelWindow + c.structureWindow + c.slack

def LabelledClassesBudgetCertificate.budgetControlled
    (c : LabelledClassesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.labelWindow + c.structureWindow + c.egfWindow + c.slack

def LabelledClassesBudgetCertificate.Ready
    (c : LabelledClassesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LabelledClassesBudgetCertificate.size
    (c : LabelledClassesBudgetCertificate) : ℕ :=
  c.labelWindow + c.structureWindow + c.egfWindow + c.slack

theorem labelledClasses_budgetCertificate_le_size
    (c : LabelledClassesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleLabelledClassesBudgetCertificate :
    LabelledClassesBudgetCertificate :=
  { labelWindow := 6
    structureWindow := 4
    egfWindow := 8
    certificateBudgetWindow := 19
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLabelledClassesBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledClassesBudgetCertificate.controlled,
      sampleLabelledClassesBudgetCertificate]
  · norm_num [LabelledClassesBudgetCertificate.budgetControlled,
      sampleLabelledClassesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLabelledClassesBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledClassesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLabelledClassesBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledClassesBudgetCertificate.controlled,
      sampleLabelledClassesBudgetCertificate]
  · norm_num [LabelledClassesBudgetCertificate.budgetControlled,
      sampleLabelledClassesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LabelledClassesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleLabelledClassesBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleLabelledClassesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.LabelledClasses
