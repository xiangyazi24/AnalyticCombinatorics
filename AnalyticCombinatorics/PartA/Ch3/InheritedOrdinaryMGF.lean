import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Inherited parameters and ordinary moment generating functions.

Finite OGF/MGF coefficient-window bookkeeping for inherited parameters.
-/

namespace AnalyticCombinatorics.PartA.Ch3.InheritedOrdinaryMGF

/-- First inherited moment numerator from ordinary coefficients. -/
def inheritedFirstMoment (coeff parameter : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total n => total + coeff n * parameter n) 0

/-- Ordinary mass prefix for a class. -/
def ordinaryMassPrefix (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + coeff n) 0

/-- Finite inherited-parameter envelope. -/
def inheritedMomentEnvelopeCheck
    (coeff parameter : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    parameter n ≤ n ∧ coeff n * parameter n ≤ n * coeff n

theorem inheritedMoment_sizeParameter :
    inheritedMomentEnvelopeCheck (fun _ => 1) (fun n => n) 16 = true ∧
      inheritedFirstMoment (fun _ => 1) (fun n => n) 4 = 10 := by
  unfold inheritedMomentEnvelopeCheck inheritedFirstMoment
  native_decide

structure OrdinaryInheritedMGFWindow where
  baseSizeWindow : ℕ
  inheritedParameterWindow : ℕ
  ordinaryMomentWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ordinaryInheritedMGFReady (w : OrdinaryInheritedMGFWindow) : Prop :=
  0 < w.baseSizeWindow ∧
    w.inheritedParameterWindow ≤
      w.baseSizeWindow + w.ordinaryMomentWindow + w.slack

def ordinaryInheritedMGFBudget (w : OrdinaryInheritedMGFWindow) : ℕ :=
  w.baseSizeWindow + w.inheritedParameterWindow +
    w.ordinaryMomentWindow + w.slack

theorem inheritedParameterWindow_le_budget
    (w : OrdinaryInheritedMGFWindow) :
    w.inheritedParameterWindow ≤ ordinaryInheritedMGFBudget w := by
  unfold ordinaryInheritedMGFBudget
  omega

def sampleOrdinaryInheritedMGFWindow : OrdinaryInheritedMGFWindow :=
  { baseSizeWindow := 5
    inheritedParameterWindow := 8
    ordinaryMomentWindow := 4
    slack := 1 }

example : ordinaryInheritedMGFReady sampleOrdinaryInheritedMGFWindow := by
  norm_num [ordinaryInheritedMGFReady, sampleOrdinaryInheritedMGFWindow]

structure InheritedOrdinaryMGFBudgetCertificate where
  baseWindow : ℕ
  parameterWindow : ℕ
  momentWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def InheritedOrdinaryMGFBudgetCertificate.controlled
    (c : InheritedOrdinaryMGFBudgetCertificate) : Prop :=
  0 < c.baseWindow ∧
    c.parameterWindow ≤ c.baseWindow + c.momentWindow + c.slack

def InheritedOrdinaryMGFBudgetCertificate.budgetControlled
    (c : InheritedOrdinaryMGFBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.baseWindow + c.parameterWindow + c.momentWindow + c.slack

def InheritedOrdinaryMGFBudgetCertificate.Ready
    (c : InheritedOrdinaryMGFBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def InheritedOrdinaryMGFBudgetCertificate.size
    (c : InheritedOrdinaryMGFBudgetCertificate) : ℕ :=
  c.baseWindow + c.parameterWindow + c.momentWindow + c.slack

theorem inheritedOrdinaryMGF_budgetCertificate_le_size
    (c : InheritedOrdinaryMGFBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleInheritedOrdinaryMGFBudgetCertificate :
    InheritedOrdinaryMGFBudgetCertificate :=
  { baseWindow := 5
    parameterWindow := 8
    momentWindow := 4
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleInheritedOrdinaryMGFBudgetCertificate.Ready := by
  constructor
  · norm_num [InheritedOrdinaryMGFBudgetCertificate.controlled,
      sampleInheritedOrdinaryMGFBudgetCertificate]
  · norm_num [InheritedOrdinaryMGFBudgetCertificate.budgetControlled,
      sampleInheritedOrdinaryMGFBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleInheritedOrdinaryMGFBudgetCertificate.certificateBudgetWindow ≤
      sampleInheritedOrdinaryMGFBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleInheritedOrdinaryMGFBudgetCertificate.Ready := by
  constructor
  · norm_num [InheritedOrdinaryMGFBudgetCertificate.controlled,
      sampleInheritedOrdinaryMGFBudgetCertificate]
  · norm_num [InheritedOrdinaryMGFBudgetCertificate.budgetControlled,
      sampleInheritedOrdinaryMGFBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List InheritedOrdinaryMGFBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleInheritedOrdinaryMGFBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleInheritedOrdinaryMGFBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.InheritedOrdinaryMGF
