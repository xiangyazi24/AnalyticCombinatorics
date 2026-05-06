import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Large deviations.
-/

namespace AnalyticCombinatorics.PartB.Ch9.LargeDeviations

/-- Quadratic finite rate model. -/
def quadraticRate (n : ℕ) : ℕ :=
  n ^ 2

/-- Finite monotonicity audit for rate functions. -/
def rateMonotoneUpTo (rate : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun n => rate n ≤ rate (n + 1)

/-- Dyadic tail bound for events at distance `t` inside size `n`. -/
def dyadicTailProxy (n t : ℕ) : ℕ :=
  2 ^ (n - t)

/-- Finite Chernoff-style tail envelope, cross-multiplied. -/
def dyadicTailEnvelopeCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    (List.range (n + 1)).all fun t =>
      dyadicTailProxy n t * 2 ^ t ≤ 2 ^ n

/-- Finite large-deviation window: monotone rate and controlled dyadic tails. -/
def LargeDeviationWindow (rate : ℕ → ℕ) (N : ℕ) : Prop :=
  rateMonotoneUpTo rate N = true ∧ dyadicTailEnvelopeCheck N = true

theorem quadraticRate_largeDeviationWindow :
    LargeDeviationWindow quadraticRate 18 := by
  unfold LargeDeviationWindow rateMonotoneUpTo dyadicTailEnvelopeCheck
    quadraticRate dyadicTailProxy
  native_decide

/-- Finite discrete convexity audit for sampled rate functions. -/
def rateConvexUpTo (rate : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun n =>
    2 * rate (n + 1) ≤ rate n + rate (n + 2)

theorem quadraticRate_convexWindow :
    rateConvexUpTo quadraticRate 16 = true := by
  unfold rateConvexUpTo quadraticRate
  native_decide

example : quadraticRate 7 = 49 := by
  unfold quadraticRate
  native_decide

example : dyadicTailProxy 8 3 = 32 := by
  unfold dyadicTailProxy
  native_decide

structure LargeDeviationsBudgetCertificate where
  rateWindow : ℕ
  transformWindow : ℕ
  tailWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LargeDeviationsBudgetCertificate.controlled
    (c : LargeDeviationsBudgetCertificate) : Prop :=
  0 < c.rateWindow ∧ c.tailWindow ≤ c.rateWindow + c.transformWindow + c.slack

def LargeDeviationsBudgetCertificate.budgetControlled
    (c : LargeDeviationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.rateWindow + c.transformWindow + c.tailWindow + c.slack

def LargeDeviationsBudgetCertificate.Ready
    (c : LargeDeviationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LargeDeviationsBudgetCertificate.size
    (c : LargeDeviationsBudgetCertificate) : ℕ :=
  c.rateWindow + c.transformWindow + c.tailWindow + c.slack

theorem largeDeviations_budgetCertificate_le_size
    (c : LargeDeviationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleLargeDeviationsBudgetCertificate :
    LargeDeviationsBudgetCertificate :=
  { rateWindow := 5
    transformWindow := 6
    tailWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLargeDeviationsBudgetCertificate.Ready := by
  constructor
  · norm_num [LargeDeviationsBudgetCertificate.controlled,
      sampleLargeDeviationsBudgetCertificate]
  · norm_num [LargeDeviationsBudgetCertificate.budgetControlled,
      sampleLargeDeviationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLargeDeviationsBudgetCertificate.certificateBudgetWindow ≤
      sampleLargeDeviationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLargeDeviationsBudgetCertificate.Ready := by
  constructor
  · norm_num [LargeDeviationsBudgetCertificate.controlled,
      sampleLargeDeviationsBudgetCertificate]
  · norm_num [LargeDeviationsBudgetCertificate.budgetControlled,
      sampleLargeDeviationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LargeDeviationsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleLargeDeviationsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleLargeDeviationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.LargeDeviations
