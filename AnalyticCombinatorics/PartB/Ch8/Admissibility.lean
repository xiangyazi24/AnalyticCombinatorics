import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Admissibility.
-/

namespace AnalyticCombinatorics.PartB.Ch8.Admissibility

/-- Finite major-arc dominance audit for saddle windows. -/
def captureDominatesCheck
    (capture localScale : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => localScale n ≤ capture n

/-- Finite minor-arc decay audit. -/
def decayDecreasesCheck (decay : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun n => decay (n + 1) ≤ decay n

def polynomialCapture (n : ℕ) : ℕ :=
  (n + 1) ^ 2

def linearLocality (n : ℕ) : ℕ :=
  n + 1

def dyadicDecay (n : ℕ) : ℕ :=
  2 ^ (20 - n)

/-- Finite admissibility statement: local control plus decreasing decay. -/
def AdmissibilityWindow
    (capture localScale decay : ℕ → ℕ) (N : ℕ) : Prop :=
  captureDominatesCheck capture localScale N = true ∧
    decayDecreasesCheck decay N = true

theorem polynomialCapture_admissibilityWindow :
    AdmissibilityWindow polynomialCapture linearLocality dyadicDecay 20 := by
  unfold AdmissibilityWindow captureDominatesCheck decayDecreasesCheck
    polynomialCapture linearLocality dyadicDecay
  native_decide

/-- Finite monotonicity audit for capture windows. -/
def captureMonotoneCheck (capture : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun n => capture n ≤ capture (n + 1)

theorem polynomialCapture_monotoneWindow :
    captureMonotoneCheck polynomialCapture 20 = true := by
  unfold captureMonotoneCheck polynomialCapture
  native_decide

example : polynomialCapture 4 = 25 := by
  unfold polynomialCapture
  native_decide

example :
    captureDominatesCheck polynomialCapture linearLocality 8 = true := by
  unfold captureDominatesCheck polynomialCapture linearLocality
  native_decide

structure AdmissibilityBudgetCertificate where
  captureWindow : ℕ
  localityWindow : ℕ
  decayWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AdmissibilityBudgetCertificate.controlled
    (c : AdmissibilityBudgetCertificate) : Prop :=
  0 < c.captureWindow ∧
    c.decayWindow ≤ c.captureWindow + c.localityWindow + c.slack

def AdmissibilityBudgetCertificate.budgetControlled
    (c : AdmissibilityBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.captureWindow + c.localityWindow + c.decayWindow + c.slack

def AdmissibilityBudgetCertificate.Ready
    (c : AdmissibilityBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AdmissibilityBudgetCertificate.size
    (c : AdmissibilityBudgetCertificate) : ℕ :=
  c.captureWindow + c.localityWindow + c.decayWindow + c.slack

theorem admissibility_budgetCertificate_le_size
    (c : AdmissibilityBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAdmissibilityBudgetCertificate : AdmissibilityBudgetCertificate :=
  { captureWindow := 5
    localityWindow := 4
    decayWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAdmissibilityBudgetCertificate.Ready := by
  constructor
  · norm_num [AdmissibilityBudgetCertificate.controlled,
      sampleAdmissibilityBudgetCertificate]
  · norm_num [AdmissibilityBudgetCertificate.budgetControlled,
      sampleAdmissibilityBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAdmissibilityBudgetCertificate.certificateBudgetWindow ≤
      sampleAdmissibilityBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAdmissibilityBudgetCertificate.Ready := by
  constructor
  · norm_num [AdmissibilityBudgetCertificate.controlled,
      sampleAdmissibilityBudgetCertificate]
  · norm_num [AdmissibilityBudgetCertificate.budgetControlled,
      sampleAdmissibilityBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AdmissibilityBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAdmissibilityBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAdmissibilityBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.Admissibility
