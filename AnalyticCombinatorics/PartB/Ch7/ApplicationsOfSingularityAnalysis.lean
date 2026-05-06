import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Applications of singularity analysis
-/

namespace AnalyticCombinatorics.PartB.Ch7.ApplicationsOfSingularityAnalysis

/-- Catalan numbers as the basic square-root singularity application. -/
def catalan (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

theorem catalan_samples :
    catalan 0 = 1 ∧ catalan 1 = 1 ∧ catalan 2 = 2 ∧
      catalan 3 = 5 ∧ catalan 4 = 14 := by
  native_decide

/-- Coarse exponential envelope for Catalan-family coefficients. -/
def catalanEnvelope (n : ℕ) : ℕ :=
  4 ^ n

theorem catalan_below_envelope_sample :
    ∀ n : Fin 10, catalan n.val ≤ catalanEnvelope n.val := by
  unfold catalan catalanEnvelope
  native_decide

/-- Subcritical composition sample envelope. -/
def subcriticalCompositionEnvelope (outer inner n : ℕ) : ℕ :=
  outer ^ n * (inner + 1)

theorem subcriticalCompositionEnvelope_pos
    {outer : ℕ} (houter : 0 < outer) (inner n : ℕ) :
    0 < subcriticalCompositionEnvelope outer inner n := by
  unfold subcriticalCompositionEnvelope
  exact Nat.mul_pos (pow_pos houter n) (Nat.succ_pos inner)

structure ApplicationWindow where
  singularityWindow : ℕ
  transferWindow : ℕ
  applicationWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ApplicationWindow.ready (w : ApplicationWindow) : Prop :=
  0 < w.singularityWindow ∧
    w.applicationWindow ≤ w.singularityWindow + w.transferWindow + w.slack

def sampleApplicationWindow : ApplicationWindow :=
  { singularityWindow := 5, transferWindow := 4,
    applicationWindow := 10, slack := 1 }

example : sampleApplicationWindow.ready := by
  norm_num [ApplicationWindow.ready, sampleApplicationWindow]

structure BudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { primaryWindow := 5, secondaryWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.ApplicationsOfSingularityAnalysis
