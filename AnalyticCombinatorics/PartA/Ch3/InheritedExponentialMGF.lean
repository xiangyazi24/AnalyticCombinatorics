import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Inherited parameters and exponential moment generating functions.

Finite EGF/MGF coefficient-window bookkeeping for labelled inherited
parameters.
-/

namespace AnalyticCombinatorics.PartA.Ch3.InheritedExponentialMGF

/-- Labelled inherited first moment numerator. -/
def inheritedExponentialFirstMoment
    (objects parameter : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total n => total + objects n * parameter n * n.factorial) 0

/-- Finite EGF inherited-parameter envelope. -/
def inheritedExponentialEnvelopeCheck
    (objects parameter : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    parameter n ≤ n ∧ objects n * parameter n ≤ n * objects n

theorem inheritedExponentialMoment_window :
    inheritedExponentialEnvelopeCheck (fun _ => 1) (fun n => n) 8 = true ∧
      inheritedExponentialFirstMoment (fun _ => 1) (fun n => n) 3 = 23 := by
  unfold inheritedExponentialEnvelopeCheck inheritedExponentialFirstMoment
  native_decide

structure ExponentialInheritedMGFWindow where
  labelWindow : ℕ
  inheritedParameterWindow : ℕ
  exponentialMomentWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def exponentialInheritedMGFReady
    (w : ExponentialInheritedMGFWindow) : Prop :=
  0 < w.labelWindow ∧
    w.inheritedParameterWindow ≤
      w.labelWindow + w.exponentialMomentWindow + w.slack

def exponentialInheritedMGFBudget
    (w : ExponentialInheritedMGFWindow) : ℕ :=
  w.labelWindow + w.inheritedParameterWindow +
    w.exponentialMomentWindow + w.slack

theorem inheritedParameterWindow_le_exponentialBudget
    (w : ExponentialInheritedMGFWindow) :
    w.inheritedParameterWindow ≤ exponentialInheritedMGFBudget w := by
  unfold exponentialInheritedMGFBudget
  omega

def sampleExponentialInheritedMGFWindow :
    ExponentialInheritedMGFWindow :=
  { labelWindow := 6
    inheritedParameterWindow := 9
    exponentialMomentWindow := 4
    slack := 1 }

example :
    exponentialInheritedMGFReady sampleExponentialInheritedMGFWindow := by
  norm_num
    [exponentialInheritedMGFReady, sampleExponentialInheritedMGFWindow]

structure InheritedExponentialMGFBudgetCertificate where
  labelWindow : ℕ
  parameterWindow : ℕ
  momentWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def InheritedExponentialMGFBudgetCertificate.controlled
    (c : InheritedExponentialMGFBudgetCertificate) : Prop :=
  0 < c.labelWindow ∧
    c.parameterWindow ≤ c.labelWindow + c.momentWindow + c.slack

def InheritedExponentialMGFBudgetCertificate.budgetControlled
    (c : InheritedExponentialMGFBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.labelWindow + c.parameterWindow + c.momentWindow + c.slack

def InheritedExponentialMGFBudgetCertificate.Ready
    (c : InheritedExponentialMGFBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def InheritedExponentialMGFBudgetCertificate.size
    (c : InheritedExponentialMGFBudgetCertificate) : ℕ :=
  c.labelWindow + c.parameterWindow + c.momentWindow + c.slack

theorem inheritedExponentialMGF_budgetCertificate_le_size
    (c : InheritedExponentialMGFBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleInheritedExponentialMGFBudgetCertificate :
    InheritedExponentialMGFBudgetCertificate :=
  { labelWindow := 6
    parameterWindow := 9
    momentWindow := 4
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleInheritedExponentialMGFBudgetCertificate.Ready := by
  constructor
  · norm_num [InheritedExponentialMGFBudgetCertificate.controlled,
      sampleInheritedExponentialMGFBudgetCertificate]
  · norm_num [InheritedExponentialMGFBudgetCertificate.budgetControlled,
      sampleInheritedExponentialMGFBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleInheritedExponentialMGFBudgetCertificate.certificateBudgetWindow ≤
      sampleInheritedExponentialMGFBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleInheritedExponentialMGFBudgetCertificate.Ready := by
  constructor
  · norm_num [InheritedExponentialMGFBudgetCertificate.controlled,
      sampleInheritedExponentialMGFBudgetCertificate]
  · norm_num [InheritedExponentialMGFBudgetCertificate.budgetControlled,
      sampleInheritedExponentialMGFBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List InheritedExponentialMGFBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleInheritedExponentialMGFBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleInheritedExponentialMGFBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.InheritedExponentialMGF
