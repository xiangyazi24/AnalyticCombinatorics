import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Index

Finite index-topic bookkeeping for cross-reference windows.
-/

namespace AnalyticCombinatorics.Index

/-- Total index coverage across entries, chapters, and cross references. -/
def indexCoverageScore
    (entries chapters crossReferences : ℕ) : ℕ :=
  entries + chapters + crossReferences

theorem indexCoverageScore_sample :
    indexCoverageScore 4 5 10 = 19 := by
  native_decide

/-- Whether cross references are supported by the indexed entries and chapters. -/
def indexCrossReferencesReady
    (entries chapters crossReferences slack : ℕ) : Bool :=
  0 < entries && crossReferences ≤ entries + chapters + slack

theorem indexCrossReferencesReady_sample :
    indexCrossReferencesReady 4 5 10 1 = true := by
  native_decide

structure IndexWindow where
  entryWindow : ℕ
  chapterWindow : ℕ
  crossReferenceWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def IndexWindow.ready (w : IndexWindow) : Prop :=
  0 < w.entryWindow ∧
    w.crossReferenceWindow ≤ w.entryWindow + w.chapterWindow + w.slack

def sampleIndexWindow : IndexWindow :=
  { entryWindow := 4, chapterWindow := 5,
    crossReferenceWindow := 10, slack := 1 }

example : sampleIndexWindow.ready := by
  norm_num [IndexWindow.ready, sampleIndexWindow]

structure BudgetCertificate where
  entryWindow : ℕ
  crossReferenceWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.entryWindow ∧
    c.crossReferenceWindow ≤ c.entryWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.entryWindow + c.crossReferenceWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.entryWindow + c.crossReferenceWindow + c.slack

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { entryWindow := 5, crossReferenceWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  norm_num [BudgetCertificate.size, sampleBudgetCertificate]

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.Index
