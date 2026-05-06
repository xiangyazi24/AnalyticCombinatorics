import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Closure properties.

Finite closure-rule bookkeeping for singularity analysis classes.
-/

namespace AnalyticCombinatorics.PartB.Ch6.ClosureProperties

/-- Sum closure for coefficient envelopes. -/
def closedSum (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  a n + b n

/-- Product closure in a finite Cauchy window. -/
def closedProduct (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + a k * b (n - k)) 0

/-- Finite closure-property check under a polynomial envelope. -/
def closurePropertyCheck
    (a b envelope : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    closedSum a b n ≤ 2 * envelope n ∧
      closedProduct a b n ≤ (n + 1) * envelope n

theorem constant_closurePropertyCheck :
    closurePropertyCheck (fun _ => 1) (fun _ => 1) (fun n => n + 1) 12 = true := by
  unfold closurePropertyCheck closedSum closedProduct
  native_decide

theorem closedProduct_constant_samples :
    closedProduct (fun _ => 1) (fun _ => 1) 4 = 5 ∧
      closedSum (fun _ => 1) (fun _ => 1) 4 = 2 := by
  unfold closedProduct closedSum
  native_decide

structure ClosurePropertiesWindow where
  baseClassWindow : ℕ
  closureRuleWindow : ℕ
  outputClassWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def closurePropertiesReady (w : ClosurePropertiesWindow) : Prop :=
  0 < w.baseClassWindow ∧
    w.outputClassWindow ≤ w.baseClassWindow + w.closureRuleWindow + w.slack

def closurePropertiesBudget (w : ClosurePropertiesWindow) : ℕ :=
  w.baseClassWindow + w.closureRuleWindow + w.outputClassWindow + w.slack

theorem outputClassWindow_le_closurePropertiesBudget
    (w : ClosurePropertiesWindow) :
    w.outputClassWindow ≤ closurePropertiesBudget w := by
  unfold closurePropertiesBudget
  omega

def sampleClosurePropertiesWindow : ClosurePropertiesWindow :=
  { baseClassWindow := 5, closureRuleWindow := 4, outputClassWindow := 8, slack := 1 }

example : closurePropertiesReady sampleClosurePropertiesWindow := by
  norm_num [closurePropertiesReady, sampleClosurePropertiesWindow]

structure ClosurePropertiesBudgetCertificate where
  baseWindow : ℕ
  closureWindow : ℕ
  outputWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ClosurePropertiesBudgetCertificate.controlled
    (c : ClosurePropertiesBudgetCertificate) : Prop :=
  0 < c.baseWindow ∧ c.outputWindow ≤ c.baseWindow + c.closureWindow + c.slack

def ClosurePropertiesBudgetCertificate.budgetControlled
    (c : ClosurePropertiesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.baseWindow + c.closureWindow + c.outputWindow + c.slack

def ClosurePropertiesBudgetCertificate.Ready
    (c : ClosurePropertiesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ClosurePropertiesBudgetCertificate.size
    (c : ClosurePropertiesBudgetCertificate) : ℕ :=
  c.baseWindow + c.closureWindow + c.outputWindow + c.slack

theorem closureProperties_budgetCertificate_le_size
    (c : ClosurePropertiesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleClosurePropertiesBudgetCertificate :
    ClosurePropertiesBudgetCertificate :=
  { baseWindow := 5
    closureWindow := 4
    outputWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleClosurePropertiesBudgetCertificate.Ready := by
  constructor
  · norm_num [ClosurePropertiesBudgetCertificate.controlled,
      sampleClosurePropertiesBudgetCertificate]
  · norm_num [ClosurePropertiesBudgetCertificate.budgetControlled,
      sampleClosurePropertiesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleClosurePropertiesBudgetCertificate.certificateBudgetWindow ≤
      sampleClosurePropertiesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleClosurePropertiesBudgetCertificate.Ready := by
  constructor
  · norm_num [ClosurePropertiesBudgetCertificate.controlled,
      sampleClosurePropertiesBudgetCertificate]
  · norm_num [ClosurePropertiesBudgetCertificate.budgetControlled,
      sampleClosurePropertiesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ClosurePropertiesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleClosurePropertiesBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleClosurePropertiesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.ClosureProperties
