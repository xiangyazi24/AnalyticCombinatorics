import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Labelled product schemas.

The file records finite split counts and label budgets for labelled product
constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch2.LabelledProductSchemas

def labelledSplits (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (n + 1)).map (fun k => (k, n - k))

def splitWeight (p : ℕ × ℕ) : ℕ :=
  p.1 + p.2

def validSplit (n : ℕ) (p : ℕ × ℕ) : Prop :=
  splitWeight p = n

theorem labelledSplits_length (n : ℕ) :
    (labelledSplits n).length = n + 1 := by
  simp [labelledSplits]

theorem validSplit_mk {n k : ℕ}
    (hk : k ≤ n) :
    validSplit n (k, n - k) := by
  unfold validSplit splitWeight
  omega

def sampleSplitMass (n : ℕ) : ℕ :=
  (labelledSplits n).map splitWeight |>.sum

example : labelledSplits 3 = [(0, 3), (1, 2), (2, 1), (3, 0)] := by
  native_decide

example : validSplit 5 (2, 3) := by
  norm_num [validSplit, splitWeight]

example : sampleSplitMass 2 = 6 := by
  native_decide

structure LabelledProductWindow where
  labels : ℕ
  leftLabels : ℕ
  rightLabels : ℕ
  splitCount : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledProductWindow.splitReady (w : LabelledProductWindow) : Prop :=
  w.leftLabels + w.rightLabels = w.labels

def LabelledProductWindow.countControlled (w : LabelledProductWindow) : Prop :=
  w.splitCount ≤ w.labels + 1 + w.slack

def LabelledProductWindow.ready (w : LabelledProductWindow) : Prop :=
  w.splitReady ∧ w.countControlled

def LabelledProductWindow.certificate (w : LabelledProductWindow) : ℕ :=
  w.labels + w.leftLabels + w.rightLabels + w.splitCount + w.slack

theorem splitCount_le_certificate (w : LabelledProductWindow) :
    w.splitCount ≤ w.certificate := by
  unfold LabelledProductWindow.certificate
  omega

def sampleLabelledProductWindow : LabelledProductWindow :=
  { labels := 5, leftLabels := 2, rightLabels := 3, splitCount := 6, slack := 0 }

example : sampleLabelledProductWindow.ready := by
  norm_num [sampleLabelledProductWindow, LabelledProductWindow.ready,
    LabelledProductWindow.splitReady, LabelledProductWindow.countControlled]


structure LabelledProductSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledProductSchemasBudgetCertificate.controlled
    (c : LabelledProductSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LabelledProductSchemasBudgetCertificate.budgetControlled
    (c : LabelledProductSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LabelledProductSchemasBudgetCertificate.Ready
    (c : LabelledProductSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LabelledProductSchemasBudgetCertificate.size
    (c : LabelledProductSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem labelledProductSchemas_budgetCertificate_le_size
    (c : LabelledProductSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLabelledProductSchemasBudgetCertificate :
    LabelledProductSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLabelledProductSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledProductSchemasBudgetCertificate.controlled,
      sampleLabelledProductSchemasBudgetCertificate]
  · norm_num [LabelledProductSchemasBudgetCertificate.budgetControlled,
      sampleLabelledProductSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLabelledProductSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledProductSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLabelledProductSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledProductSchemasBudgetCertificate.controlled,
      sampleLabelledProductSchemasBudgetCertificate]
  · norm_num [LabelledProductSchemasBudgetCertificate.budgetControlled,
      sampleLabelledProductSchemasBudgetCertificate]

example :
    sampleLabelledProductSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledProductSchemasBudgetCertificate.size := by
  apply labelledProductSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LabelledProductSchemasBudgetCertificate.controlled,
      sampleLabelledProductSchemasBudgetCertificate]
  · norm_num [LabelledProductSchemasBudgetCertificate.budgetControlled,
      sampleLabelledProductSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LabelledProductSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLabelledProductSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLabelledProductSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.LabelledProductSchemas
