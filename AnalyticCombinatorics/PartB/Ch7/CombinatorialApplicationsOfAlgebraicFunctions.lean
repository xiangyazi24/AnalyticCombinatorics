import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Combinatorial applications of algebraic functions
-/

namespace AnalyticCombinatorics.PartB.Ch7.CombinatorialApplicationsOfAlgebraicFunctions

/-- Algebraic counting model for Catalan-like applications. -/
def algebraicApplicationCatalan (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

theorem algebraicApplicationCatalan_five :
    algebraicApplicationCatalan 5 = 42 := by
  native_decide

/-- Algebraic substitution envelope for a finite application family. -/
def algebraicApplicationEnvelope (branchCount transferScale : ℕ) : ℕ :=
  branchCount * transferScale

theorem algebraicApplicationEnvelope_sample :
    algebraicApplicationEnvelope 6 7 = 42 := by
  native_decide

structure AlgebraicApplicationWindow where
  algebraicWindow : ℕ
  combinatorialWindow : ℕ
  transferWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlgebraicApplicationWindow.ready
    (w : AlgebraicApplicationWindow) : Prop :=
  0 < w.algebraicWindow ∧
    w.combinatorialWindow ≤ w.algebraicWindow + w.transferWindow + w.slack

def sampleAlgebraicApplicationWindow : AlgebraicApplicationWindow :=
  { algebraicWindow := 4, combinatorialWindow := 7,
    transferWindow := 3, slack := 0 }

example : sampleAlgebraicApplicationWindow.ready := by
  norm_num [AlgebraicApplicationWindow.ready,
    sampleAlgebraicApplicationWindow]

structure BudgetCertificate where
  algebraicWindow : ℕ
  applicationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.algebraicWindow ∧ c.applicationWindow ≤ c.algebraicWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.algebraicWindow + c.applicationWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.algebraicWindow + c.applicationWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { algebraicWindow := 5, applicationWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  have h : sampleBudgetCertificate.Ready := by
    constructor
    · norm_num [BudgetCertificate.controlled,
        sampleBudgetCertificate]
    · norm_num [BudgetCertificate.budgetControlled,
        sampleBudgetCertificate]
  exact h.2

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

end AnalyticCombinatorics.PartB.Ch7.CombinatorialApplicationsOfAlgebraicFunctions
