import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Gamma function.
-/

namespace AnalyticCombinatorics.AppB.GammaFunction

/-- Natural-number Gamma model: `Gamma(n + 1) = n!`. -/
def gammaNat (n : ℕ) : ℕ :=
  n.factorial

theorem gammaNat_zero :
    gammaNat 0 = 1 := by
  simp [gammaNat]

theorem gammaNat_succ (n : ℕ) :
    gammaNat (n + 1) = (n + 1) * gammaNat n := by
  simp [gammaNat, Nat.factorial_succ]

/-- Finite recurrence audit for the discrete Gamma model. -/
def gammaRecurrenceCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => gammaNat (n + 1) = (n + 1) * gammaNat n

/-- Finite Stirling-scale lower envelope, deliberately coarse. -/
def gammaExponentialEnvelopeCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => 1 ≤ gammaNat n ∧ gammaNat n ≤ (n + 1) ^ n

def GammaWindow (N : ℕ) : Prop :=
  gammaRecurrenceCheck N = true ∧ gammaExponentialEnvelopeCheck N = true

theorem gammaNat_samples :
    gammaNat 0 = 1 ∧
    gammaNat 1 = 1 ∧
    gammaNat 2 = 2 ∧
    gammaNat 3 = 6 ∧
    gammaNat 4 = 24 := by
  unfold gammaNat
  native_decide

example : gammaRecurrenceCheck 6 = true := by
  unfold gammaRecurrenceCheck gammaNat
  native_decide

theorem gammaNat_window :
    GammaWindow 10 := by
  unfold GammaWindow gammaRecurrenceCheck gammaExponentialEnvelopeCheck gammaNat
  native_decide

/-- Prefix sum of the discrete Gamma model. -/
def gammaPrefixSum (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + gammaNat n) 0

theorem gammaPrefixSum_zero :
    gammaPrefixSum 0 = 1 := by
  simp [gammaPrefixSum, gammaNat]

example : gammaPrefixSum 4 = 34 := by
  unfold gammaPrefixSum gammaNat
  native_decide

def GammaPrefixWindow (N total : ℕ) : Prop :=
  gammaPrefixSum N = total

theorem gammaNat_prefixWindow :
    GammaPrefixWindow 5 154 := by
  unfold GammaPrefixWindow gammaPrefixSum gammaNat
  native_decide

structure GammaFunctionBudgetCertificate where
  recurrenceWindow : ℕ
  integralWindow : ℕ
  asymptoticWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GammaFunctionBudgetCertificate.controlled
    (c : GammaFunctionBudgetCertificate) : Prop :=
  0 < c.recurrenceWindow ∧
    c.asymptoticWindow ≤ c.recurrenceWindow + c.integralWindow + c.slack

def GammaFunctionBudgetCertificate.budgetControlled
    (c : GammaFunctionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.recurrenceWindow + c.integralWindow + c.asymptoticWindow + c.slack

def GammaFunctionBudgetCertificate.Ready
    (c : GammaFunctionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GammaFunctionBudgetCertificate.size
    (c : GammaFunctionBudgetCertificate) : ℕ :=
  c.recurrenceWindow + c.integralWindow + c.asymptoticWindow + c.slack

theorem gammaFunction_budgetCertificate_le_size
    (c : GammaFunctionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleGammaFunctionBudgetCertificate :
    GammaFunctionBudgetCertificate :=
  { recurrenceWindow := 5
    integralWindow := 6
    asymptoticWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example : sampleGammaFunctionBudgetCertificate.Ready := by
  constructor
  · norm_num [GammaFunctionBudgetCertificate.controlled,
      sampleGammaFunctionBudgetCertificate]
  · norm_num [GammaFunctionBudgetCertificate.budgetControlled,
      sampleGammaFunctionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleGammaFunctionBudgetCertificate.Ready := by
  constructor
  · norm_num [GammaFunctionBudgetCertificate.controlled,
      sampleGammaFunctionBudgetCertificate]
  · norm_num [GammaFunctionBudgetCertificate.budgetControlled,
      sampleGammaFunctionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGammaFunctionBudgetCertificate.certificateBudgetWindow ≤
      sampleGammaFunctionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List GammaFunctionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleGammaFunctionBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleGammaFunctionBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.GammaFunction
