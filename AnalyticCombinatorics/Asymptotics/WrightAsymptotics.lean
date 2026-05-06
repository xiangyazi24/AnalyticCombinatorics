import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Wright asymptotics.
-/

namespace AnalyticCombinatorics.Asymptotics.WrightAsymptotics

/-- A simple exponential envelope for partition-growth windows. -/
def exponentialProxy (base n : ℕ) : ℕ :=
  base ^ n

/-- Prefix sum used for Wright-style cumulative partition estimates. -/
def prefixSumNat (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + a k) 0

/-- Finite exponential-ratio envelope for partition-like coefficient data. -/
def exponentialRatioEnvelope
    (a : ℕ → ℕ) (base N : ℕ) : Bool :=
  (List.range N).all fun n => a (n + 1) ≤ base * a n

/-- Finite Wright-style window: coefficient and prefix sums share an envelope. -/
def WrightWindow (a envelope : ℕ → ℕ) (base N : ℕ) : Prop :=
  exponentialRatioEnvelope a base N = true ∧
    ((List.range (N + 1)).all fun n =>
      a n ≤ envelope n ∧ prefixSumNat a n ≤ (n + 1) * envelope n) = true

theorem exponentialProxy_ratioEnvelope :
    exponentialRatioEnvelope (exponentialProxy 2) 2 20 = true := by
  unfold exponentialRatioEnvelope exponentialProxy
  native_decide

theorem exponentialProxy_wrightWindow :
    WrightWindow (exponentialProxy 2) (exponentialProxy 2) 2 20 := by
  unfold WrightWindow exponentialRatioEnvelope prefixSumNat exponentialProxy
  native_decide

/-- Finite monotonicity audit for cumulative Wright-style proxies. -/
def prefixSumMonotoneCheck (a : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun n => prefixSumNat a n ≤ prefixSumNat a (n + 1)

theorem exponentialProxy_prefixMonotoneWindow :
    prefixSumMonotoneCheck (exponentialProxy 3) 16 = true := by
  unfold prefixSumMonotoneCheck prefixSumNat exponentialProxy
  native_decide

example : prefixSumNat (exponentialProxy 2) 4 = 31 := by
  unfold prefixSumNat exponentialProxy
  native_decide

example : exponentialRatioEnvelope (exponentialProxy 3) 3 8 = true := by
  unfold exponentialRatioEnvelope exponentialProxy
  native_decide

structure WrightAsymptoticsBudgetCertificate where
  saddleWindow : ℕ
  partitionWindow : ℕ
  exponentialWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WrightAsymptoticsBudgetCertificate.controlled
    (c : WrightAsymptoticsBudgetCertificate) : Prop :=
  0 < c.saddleWindow ∧
    c.exponentialWindow ≤ c.saddleWindow + c.partitionWindow + c.slack

def WrightAsymptoticsBudgetCertificate.budgetControlled
    (c : WrightAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleWindow + c.partitionWindow + c.exponentialWindow + c.slack

def WrightAsymptoticsBudgetCertificate.Ready
    (c : WrightAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WrightAsymptoticsBudgetCertificate.size
    (c : WrightAsymptoticsBudgetCertificate) : ℕ :=
  c.saddleWindow + c.partitionWindow + c.exponentialWindow + c.slack

theorem wrightAsymptotics_budgetCertificate_le_size
    (c : WrightAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleWrightAsymptoticsBudgetCertificate :
    WrightAsymptoticsBudgetCertificate :=
  { saddleWindow := 5
    partitionWindow := 6
    exponentialWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example : sampleWrightAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [WrightAsymptoticsBudgetCertificate.controlled,
      sampleWrightAsymptoticsBudgetCertificate]
  · norm_num [WrightAsymptoticsBudgetCertificate.budgetControlled,
      sampleWrightAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for Wright asymptotics certificates. -/
def wrightAsymptoticsBudgetCertificateListReady
    (data : List WrightAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c =>
    0 < c.saddleWindow &&
      c.exponentialWindow ≤ c.saddleWindow + c.partitionWindow + c.slack &&
        c.certificateBudgetWindow ≤
          c.saddleWindow + c.partitionWindow + c.exponentialWindow + c.slack

theorem wrightAsymptoticsBudgetCertificateList_readyWindow :
    wrightAsymptoticsBudgetCertificateListReady
      [sampleWrightAsymptoticsBudgetCertificate,
       { saddleWindow := 4, partitionWindow := 5, exponentialWindow := 8,
         certificateBudgetWindow := 18, slack := 1 }] = true := by
  unfold wrightAsymptoticsBudgetCertificateListReady
    sampleWrightAsymptoticsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleWrightAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [WrightAsymptoticsBudgetCertificate.controlled,
      sampleWrightAsymptoticsBudgetCertificate]
  · norm_num [WrightAsymptoticsBudgetCertificate.budgetControlled,
      sampleWrightAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWrightAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleWrightAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List WrightAsymptoticsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleWrightAsymptoticsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleWrightAsymptoticsBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.WrightAsymptotics
