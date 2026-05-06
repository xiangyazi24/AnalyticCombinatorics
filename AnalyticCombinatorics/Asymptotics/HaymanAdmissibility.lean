import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Hayman admissibility.
-/

namespace AnalyticCombinatorics.Asymptotics.HaymanAdmissibility

/-- Finite positivity check for admissible coefficient models. -/
def positiveUpTo (a : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => 0 < a n

/-- Finite monotonicity check for coefficient growth. -/
def nondecreasingUpTo (a : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun n => a n ≤ a (n + 1)

/-- Sampled log-convexity, a common coefficient-side Hayman condition. -/
def logConvexUpTo (a : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun n =>
    if n = 0 then true else a n * a n ≤ a (n - 1) * a (n + 1)

/-- Finite Hayman-admissibility window for coefficient models. -/
def HaymanWindow (a : ℕ → ℕ) (N : ℕ) : Prop :=
  positiveUpTo a N = true ∧
    nondecreasingUpTo a N = true ∧
      logConvexUpTo a N = true

def factorialShiftModel (n : ℕ) : ℕ :=
  (n + 1).factorial

theorem factorialShift_haymanWindow :
    HaymanWindow factorialShiftModel 10 := by
  unfold HaymanWindow positiveUpTo nondecreasingUpTo logConvexUpTo
    factorialShiftModel
  native_decide

theorem exponential_haymanWindow :
    HaymanWindow (fun n => 2 ^ n) 16 := by
  unfold HaymanWindow positiveUpTo nondecreasingUpTo logConvexUpTo
  native_decide

/-- Finite ratio lower-bound audit for Hayman coefficient proxies. -/
def ratioLowerBoundCheck (a : ℕ → ℕ) (factor N : ℕ) : Bool :=
  (List.range N).all fun n => factor * a n ≤ a (n + 1)

theorem exponential_ratioLowerBoundWindow :
    ratioLowerBoundCheck (fun n => 2 ^ n) 2 16 = true := by
  unfold ratioLowerBoundCheck
  native_decide

example : positiveUpTo factorialShiftModel 6 = true := by
  unfold positiveUpTo factorialShiftModel
  native_decide

example : ratioLowerBoundCheck (fun n => 2 ^ n) 2 6 = true := by
  unfold ratioLowerBoundCheck
  native_decide

structure HaymanAdmissibilityBudgetCertificate where
  captureWindow : ℕ
  localityWindow : ℕ
  decayWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HaymanAdmissibilityBudgetCertificate.controlled
    (c : HaymanAdmissibilityBudgetCertificate) : Prop :=
  0 < c.captureWindow ∧
    c.decayWindow ≤ c.captureWindow + c.localityWindow + c.slack

def HaymanAdmissibilityBudgetCertificate.budgetControlled
    (c : HaymanAdmissibilityBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.captureWindow + c.localityWindow + c.decayWindow + c.slack

def HaymanAdmissibilityBudgetCertificate.Ready
    (c : HaymanAdmissibilityBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HaymanAdmissibilityBudgetCertificate.size
    (c : HaymanAdmissibilityBudgetCertificate) : ℕ :=
  c.captureWindow + c.localityWindow + c.decayWindow + c.slack

theorem haymanAdmissibility_budgetCertificate_le_size
    (c : HaymanAdmissibilityBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleHaymanAdmissibilityBudgetCertificate :
    HaymanAdmissibilityBudgetCertificate :=
  { captureWindow := 5
    localityWindow := 6
    decayWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example : sampleHaymanAdmissibilityBudgetCertificate.Ready := by
  constructor
  · norm_num [HaymanAdmissibilityBudgetCertificate.controlled,
      sampleHaymanAdmissibilityBudgetCertificate]
  · norm_num [HaymanAdmissibilityBudgetCertificate.budgetControlled,
      sampleHaymanAdmissibilityBudgetCertificate]

/-- Finite executable readiness audit for Hayman admissibility certificates. -/
def haymanAdmissibilityCertificateListReady
    (certs : List HaymanAdmissibilityBudgetCertificate) : Bool :=
  certs.all fun c =>
    0 < c.captureWindow &&
      c.decayWindow ≤ c.captureWindow + c.localityWindow + c.slack &&
        c.certificateBudgetWindow ≤
          c.captureWindow + c.localityWindow + c.decayWindow + c.slack

theorem haymanAdmissibilityCertificateList_readyWindow :
    haymanAdmissibilityCertificateListReady
      [{ captureWindow := 3, localityWindow := 4, decayWindow := 6,
         certificateBudgetWindow := 13, slack := 0 },
       { captureWindow := 5, localityWindow := 6, decayWindow := 10,
         certificateBudgetWindow := 22, slack := 1 }] = true := by
  unfold haymanAdmissibilityCertificateListReady
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleHaymanAdmissibilityBudgetCertificate.Ready := by
  constructor
  · norm_num [HaymanAdmissibilityBudgetCertificate.controlled,
      sampleHaymanAdmissibilityBudgetCertificate]
  · norm_num [HaymanAdmissibilityBudgetCertificate.budgetControlled,
      sampleHaymanAdmissibilityBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHaymanAdmissibilityBudgetCertificate.certificateBudgetWindow ≤
      sampleHaymanAdmissibilityBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List HaymanAdmissibilityBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHaymanAdmissibilityBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleHaymanAdmissibilityBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.HaymanAdmissibility
