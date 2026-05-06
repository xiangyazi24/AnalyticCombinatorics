import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Large deviation principle
-/

namespace AnalyticCombinatorics.Asymptotics.LargeDeviationPrinciple

/-- Exponential-rate envelope after clearing analytic constants. -/
def rateEnvelope (rate n : ℕ) : ℕ :=
  rate ^ n

theorem rateEnvelope_zero (rate : ℕ) :
    rateEnvelope rate 0 = 1 := by
  simp [rateEnvelope]

theorem rateEnvelope_succ (rate n : ℕ) :
    rateEnvelope rate (n + 1) = rate * rateEnvelope rate n := by
  simp [rateEnvelope, pow_succ, Nat.mul_comm]

/-- Tail bound audit: sampled tails stay below an exponential envelope. -/
def tailBelowRateEnvelope (tail : ℕ → ℕ) (rate N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => tail n ≤ rateEnvelope rate n

theorem geometricTailBelowEnvelope :
    tailBelowRateEnvelope (fun n => 2 ^ n) 2 12 = true := by
  unfold tailBelowRateEnvelope rateEnvelope
  native_decide

def chernoffProxy (mean threshold : ℕ) : ℕ :=
  if mean ≤ threshold then threshold - mean else 0

theorem chernoffProxy_zero_at_mean (mean : ℕ) :
    chernoffProxy mean mean = 0 := by
  simp [chernoffProxy]

structure LargeDeviationWindow where
  rateWindow : ℕ
  tailWindow : ℕ
  exponentialWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LargeDeviationWindow.ready (w : LargeDeviationWindow) : Prop :=
  0 < w.rateWindow ∧
    w.tailWindow ≤ w.rateWindow + w.exponentialWindow + w.slack

def sampleLargeDeviationWindow : LargeDeviationWindow :=
  { rateWindow := 4, tailWindow := 7, exponentialWindow := 3, slack := 0 }

example : sampleLargeDeviationWindow.ready := by
  norm_num [LargeDeviationWindow.ready, sampleLargeDeviationWindow]

structure BudgetCertificate where
  rateWindow : ℕ
  tailWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.rateWindow ∧ c.tailWindow ≤ c.rateWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.rateWindow + c.tailWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.rateWindow + c.tailWindow + c.slack

theorem largeDeviationPrinciple_budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { rateWindow := 5, tailWindow := 6, certificateBudgetWindow := 12,
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.LargeDeviationPrinciple
