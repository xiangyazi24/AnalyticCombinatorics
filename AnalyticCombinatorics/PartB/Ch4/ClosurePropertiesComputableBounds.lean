import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Closure properties and computable bounds.
-/

namespace AnalyticCombinatorics.PartB.Ch4.ClosurePropertiesComputableBounds

/-- Pointwise sum of coefficient bounds. -/
def sumCoeff (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  a n + b n

/-- Cauchy product coefficient. -/
def productCoeff (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + a k * b (n - k)) 0

/-- Finite closure audit for sums and products under an envelope. -/
def closureBoundCheck
    (a b envelope : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    sumCoeff a b n ≤ 2 * envelope n ∧ productCoeff a b n ≤ (n + 1) * envelope n

theorem constant_closureBoundCheck :
    closureBoundCheck (fun _ => 1) (fun _ => 1) (fun n => n + 1) 12 = true := by
  unfold closureBoundCheck sumCoeff productCoeff
  native_decide

/-- Scalar multiplication of a coefficient sequence. -/
def scalarCoeff (scale : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  scale * a n

/-- Finite audit that scalar multiplication preserves a computable envelope. -/
def scalarBoundCheck
    (scale : ℕ) (a envelope : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    scalarCoeff scale a n ≤ scale * envelope n

theorem scalar_constantBoundCheck :
    scalarBoundCheck 3 (fun n => n + 1) (fun n => n + 2) 10 = true := by
  unfold scalarBoundCheck scalarCoeff
  native_decide

structure ClosurePropertiesComputableBoundsBudgetCertificate where
  closureWindow : ℕ
  majorantWindow : ℕ
  boundWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ClosurePropertiesComputableBoundsBudgetCertificate.controlled
    (c : ClosurePropertiesComputableBoundsBudgetCertificate) : Prop :=
  0 < c.closureWindow ∧
    c.boundWindow ≤ c.closureWindow + c.majorantWindow + c.slack

def ClosurePropertiesComputableBoundsBudgetCertificate.budgetControlled
    (c : ClosurePropertiesComputableBoundsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.closureWindow + c.majorantWindow + c.boundWindow + c.slack

def ClosurePropertiesComputableBoundsBudgetCertificate.Ready
    (c : ClosurePropertiesComputableBoundsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ClosurePropertiesComputableBoundsBudgetCertificate.size
    (c : ClosurePropertiesComputableBoundsBudgetCertificate) : ℕ :=
  c.closureWindow + c.majorantWindow + c.boundWindow + c.slack

theorem closurePropertiesComputableBounds_budgetCertificate_le_size
    (c : ClosurePropertiesComputableBoundsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleClosurePropertiesComputableBoundsBudgetCertificate :
    ClosurePropertiesComputableBoundsBudgetCertificate :=
  { closureWindow := 5
    majorantWindow := 6
    boundWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleClosurePropertiesComputableBoundsBudgetCertificate.Ready := by
  constructor
  · norm_num [ClosurePropertiesComputableBoundsBudgetCertificate.controlled,
      sampleClosurePropertiesComputableBoundsBudgetCertificate]
  · norm_num [ClosurePropertiesComputableBoundsBudgetCertificate.budgetControlled,
      sampleClosurePropertiesComputableBoundsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleClosurePropertiesComputableBoundsBudgetCertificate.certificateBudgetWindow ≤
      sampleClosurePropertiesComputableBoundsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleClosurePropertiesComputableBoundsBudgetCertificate.Ready := by
  constructor
  · norm_num [ClosurePropertiesComputableBoundsBudgetCertificate.controlled,
      sampleClosurePropertiesComputableBoundsBudgetCertificate]
  · norm_num
      [ClosurePropertiesComputableBoundsBudgetCertificate.budgetControlled,
        sampleClosurePropertiesComputableBoundsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List ClosurePropertiesComputableBoundsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleClosurePropertiesComputableBoundsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleClosurePropertiesComputableBoundsBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleClosurePropertiesComputableBoundsBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch4.ClosurePropertiesComputableBounds
