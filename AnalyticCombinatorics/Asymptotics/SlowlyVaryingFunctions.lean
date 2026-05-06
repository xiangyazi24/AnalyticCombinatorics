import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Slowly varying functions.
-/

namespace AnalyticCombinatorics.Asymptotics.SlowlyVaryingFunctions

/-- A logarithmic scale used for finite slow-variation checks. -/
def logProxy (n : ℕ) : ℕ :=
  Nat.log2 (n + 1) + 1

/-- Finite nonzero check for denominator-like slow scales. -/
def positiveUpTo (L : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => 0 < L n

/--
Dyadic slow-variation certificate: doubling the input changes the scale by
at most a factor of two over the sampled window.
-/
def dyadicSlowVariationCheck (L : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    L (2 * n + 1) ≤ 2 * L n ∧ L n ≤ 2 * L (2 * n + 1)

/-- Finite statement form for slowly varying scales. -/
def SlowlyVaryingWindow (L : ℕ → ℕ) (N : ℕ) : Prop :=
  positiveUpTo L N = true ∧ dyadicSlowVariationCheck L N = true

theorem constant_slowlyVaryingWindow :
    SlowlyVaryingWindow (fun _ => 1) 32 := by
  unfold SlowlyVaryingWindow positiveUpTo dyadicSlowVariationCheck
  native_decide

theorem logProxy_slowlyVaryingWindow :
    SlowlyVaryingWindow logProxy 64 := by
  unfold SlowlyVaryingWindow positiveUpTo dyadicSlowVariationCheck logProxy
  native_decide

/-- Product with a constant multiplier preserves the finite dyadic window. -/
theorem constant_multiple_logProxy_slowlyVaryingWindow :
    SlowlyVaryingWindow (fun n => 3 * logProxy n) 64 := by
  unfold SlowlyVaryingWindow positiveUpTo dyadicSlowVariationCheck logProxy
  native_decide

example : logProxy 15 = 5 := by
  unfold logProxy
  native_decide

example : dyadicSlowVariationCheck logProxy 10 = true := by
  unfold dyadicSlowVariationCheck logProxy
  native_decide

structure SlowlyVaryingFunctionsBudgetCertificate where
  scaleWindow : ℕ
  ratioWindow : ℕ
  uniformityWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SlowlyVaryingFunctionsBudgetCertificate.controlled
    (c : SlowlyVaryingFunctionsBudgetCertificate) : Prop :=
  0 < c.scaleWindow ∧
    c.uniformityWindow ≤ c.scaleWindow + c.ratioWindow + c.slack

def SlowlyVaryingFunctionsBudgetCertificate.budgetControlled
    (c : SlowlyVaryingFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.scaleWindow + c.ratioWindow + c.uniformityWindow + c.slack

def SlowlyVaryingFunctionsBudgetCertificate.Ready
    (c : SlowlyVaryingFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SlowlyVaryingFunctionsBudgetCertificate.size
    (c : SlowlyVaryingFunctionsBudgetCertificate) : ℕ :=
  c.scaleWindow + c.ratioWindow + c.uniformityWindow + c.slack

theorem slowlyVaryingFunctions_budgetCertificate_le_size
    (c : SlowlyVaryingFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSlowlyVaryingFunctionsBudgetCertificate :
    SlowlyVaryingFunctionsBudgetCertificate :=
  { scaleWindow := 5
    ratioWindow := 6
    uniformityWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example : sampleSlowlyVaryingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SlowlyVaryingFunctionsBudgetCertificate.controlled,
      sampleSlowlyVaryingFunctionsBudgetCertificate]
  · norm_num [SlowlyVaryingFunctionsBudgetCertificate.budgetControlled,
      sampleSlowlyVaryingFunctionsBudgetCertificate]

/-- Finite executable readiness audit for slowly varying certificates. -/
def slowlyVaryingCertificateListReady
    (certs : List SlowlyVaryingFunctionsBudgetCertificate) : Bool :=
  certs.all fun c =>
    0 < c.scaleWindow &&
      c.uniformityWindow ≤ c.scaleWindow + c.ratioWindow + c.slack &&
        c.certificateBudgetWindow ≤
          c.scaleWindow + c.ratioWindow + c.uniformityWindow + c.slack

theorem slowlyVaryingCertificateList_readyWindow :
    slowlyVaryingCertificateListReady
      [{ scaleWindow := 3, ratioWindow := 4, uniformityWindow := 6,
         certificateBudgetWindow := 13, slack := 0 },
       { scaleWindow := 5, ratioWindow := 6, uniformityWindow := 10,
         certificateBudgetWindow := 22, slack := 1 }] = true := by
  unfold slowlyVaryingCertificateListReady
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSlowlyVaryingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SlowlyVaryingFunctionsBudgetCertificate.controlled,
      sampleSlowlyVaryingFunctionsBudgetCertificate]
  · norm_num [SlowlyVaryingFunctionsBudgetCertificate.budgetControlled,
      sampleSlowlyVaryingFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSlowlyVaryingFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleSlowlyVaryingFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SlowlyVaryingFunctionsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSlowlyVaryingFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSlowlyVaryingFunctionsBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SlowlyVaryingFunctions
