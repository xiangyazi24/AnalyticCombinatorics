import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Bibliography

Finite citation-topic bookkeeping for references used by the formalization.
-/

namespace AnalyticCombinatorics.Bibliography

/-- Total topic coverage represented by a finite bibliographic slice. -/
def bibliographicCoverageScore
    (symbolic analytic probability : ℕ) : ℕ :=
  symbolic + analytic + probability

theorem bibliographicCoverageScore_sample :
    bibliographicCoverageScore 4 5 10 = 19 := by
  native_decide

/-- Whether a bibliographic slice covers probability references within slack. -/
def bibliographicSliceReady
    (symbolic analytic probability slack : ℕ) : Bool :=
  0 < symbolic && probability ≤ symbolic + analytic + slack

theorem bibliographicSliceReady_sample :
    bibliographicSliceReady 4 5 10 1 = true := by
  native_decide

structure BibliographicWindow where
  symbolicReferenceWindow : ℕ
  analyticReferenceWindow : ℕ
  probabilityReferenceWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BibliographicWindow.ready (w : BibliographicWindow) : Prop :=
  0 < w.symbolicReferenceWindow ∧
    w.probabilityReferenceWindow ≤
      w.symbolicReferenceWindow + w.analyticReferenceWindow + w.slack

def sampleBibliographicWindow : BibliographicWindow :=
  { symbolicReferenceWindow := 4, analyticReferenceWindow := 5,
    probabilityReferenceWindow := 10, slack := 1 }

example : sampleBibliographicWindow.ready := by
  norm_num [BibliographicWindow.ready, sampleBibliographicWindow]

structure BudgetCertificate where
  referenceWindow : ℕ
  topicWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.referenceWindow ∧ c.topicWindow ≤ c.referenceWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.referenceWindow + c.topicWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.referenceWindow + c.topicWindow + c.slack

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { referenceWindow := 5, topicWindow := 6,
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

end AnalyticCombinatorics.Bibliography
