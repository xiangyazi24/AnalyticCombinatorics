import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# An invitation to analytic combinatorics

Finite bridge windows for the introductory examples connecting counting,
generating functions, and asymptotics.
-/

namespace AnalyticCombinatorics.InvitationToAnalyticCombinatorics

/-- Introductory bridge score from counting to generating functions to asymptotics. -/
def invitationBridgeScore (counting gf asymptotic : ℕ) : ℕ :=
  counting + gf + asymptotic

theorem invitationBridgeScore_sample :
    invitationBridgeScore 4 5 10 = 19 := by
  native_decide

/-- Readiness check for the opening examples after clearing all finite windows. -/
def invitationExamplesReady
    (counting gf asymptotic slack : ℕ) : Bool :=
  0 < counting && asymptotic ≤ counting + gf + slack

theorem invitationExamplesReady_sample :
    invitationExamplesReady 4 5 10 1 = true := by
  native_decide

structure InvitationWindow where
  countingWindow : ℕ
  generatingFunctionWindow : ℕ
  asymptoticWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def InvitationWindow.ready (w : InvitationWindow) : Prop :=
  0 < w.countingWindow ∧
    w.asymptoticWindow ≤
      w.countingWindow + w.generatingFunctionWindow + w.slack

def sampleInvitationWindow : InvitationWindow :=
  { countingWindow := 4, generatingFunctionWindow := 5,
    asymptoticWindow := 10, slack := 1 }

example : sampleInvitationWindow.ready := by
  norm_num [InvitationWindow.ready, sampleInvitationWindow]

structure BudgetCertificate where
  countingWindow : ℕ
  asymptoticWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.countingWindow ∧ c.asymptoticWindow ≤ c.countingWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.countingWindow + c.asymptoticWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.countingWindow + c.asymptoticWindow + c.slack

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { countingWindow := 5, asymptoticWindow := 6,
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

end AnalyticCombinatorics.InvitationToAnalyticCombinatorics
