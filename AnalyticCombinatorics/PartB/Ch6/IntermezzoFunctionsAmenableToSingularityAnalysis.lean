import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Intermezzo: functions amenable to singularity analysis
-/

namespace AnalyticCombinatorics.PartB.Ch6.IntermezzoFunctionsAmenableToSingularityAnalysis

/-- Finite local expansion data around a dominant singularity. -/
structure LocalExpansion where
  analyticOrder : ℕ
  singularOrder : ℕ
  coefficientBound : ℕ
deriving DecidableEq, Repr

def LocalExpansion.ready (e : LocalExpansion) : Prop :=
  0 < e.analyticOrder ∧ 0 < e.coefficientBound

def sampleLocalExpansion : LocalExpansion :=
  { analyticOrder := 3, singularOrder := 2, coefficientBound := 8 }

theorem sampleLocalExpansion_ready :
    sampleLocalExpansion.ready := by
  norm_num [LocalExpansion.ready, sampleLocalExpansion]

/-- A finite amenability audit: expansion order and coefficient bound are positive. -/
def amenableExpansionListReady (data : List LocalExpansion) : Bool :=
  data.all fun e => 0 < e.analyticOrder && 0 < e.coefficientBound

theorem amenableExpansionListReady_sample :
    amenableExpansionListReady
      [sampleLocalExpansion,
       { analyticOrder := 1, singularOrder := 0, coefficientBound := 1 }] =
        true := by
  unfold amenableExpansionListReady sampleLocalExpansion
  native_decide

/-- Transfer envelope for an amenable singular expansion. -/
def amenableTransferEnvelope (e : LocalExpansion) (radiusInv n : ℕ) : ℕ :=
  e.coefficientBound * (n + e.singularOrder + 1) * radiusInv ^ n

theorem amenableTransferEnvelope_pos
    (e : LocalExpansion) (h : e.ready) {radiusInv : ℕ}
    (hr : 0 < radiusInv) (n : ℕ) :
    0 < amenableTransferEnvelope e radiusInv n := by
  unfold amenableTransferEnvelope
  exact Nat.mul_pos
    (Nat.mul_pos h.2 (Nat.succ_pos (n + e.singularOrder)))
    (pow_pos hr n)

structure AmenableFunctionWindow where
  localExpansionWindow : ℕ
  transferWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AmenableFunctionWindow.controlled (w : AmenableFunctionWindow) : Prop :=
  0 < w.localExpansionWindow ∧
    w.transferWindow ≤ w.localExpansionWindow + w.slack

def AmenableFunctionWindow.budgetControlled
    (w : AmenableFunctionWindow) : Prop :=
  w.certificateBudgetWindow ≤
    w.localExpansionWindow + w.transferWindow + w.slack

def AmenableFunctionWindow.Ready (w : AmenableFunctionWindow) : Prop :=
  w.controlled ∧ w.budgetControlled

def AmenableFunctionWindow.size (w : AmenableFunctionWindow) : ℕ :=
  w.localExpansionWindow + w.transferWindow + w.slack

def sampleAmenableFunctionWindow : AmenableFunctionWindow :=
  { localExpansionWindow := 2
    transferWindow := 3
    certificateBudgetWindow := 6
    slack := 1 }

example : sampleAmenableFunctionWindow.Ready := by
  constructor <;> norm_num
    [AmenableFunctionWindow.controlled,
      AmenableFunctionWindow.budgetControlled, sampleAmenableFunctionWindow]

theorem window_budgetCertificate_le_size
    (w : AmenableFunctionWindow) (h : w.Ready) :
    w.certificateBudgetWindow ≤ w.size := by
  exact h.2

theorem sampleWindow_le_size :
    sampleAmenableFunctionWindow.certificateBudgetWindow ≤
      sampleAmenableFunctionWindow.size := by
  have h : sampleAmenableFunctionWindow.Ready := by
    constructor <;> norm_num
      [AmenableFunctionWindow.controlled, AmenableFunctionWindow.budgetControlled,
        sampleAmenableFunctionWindow]
  exact h.2

abbrev BudgetCertificate := AmenableFunctionWindow

def sampleBudgetCertificate : BudgetCertificate :=
  sampleAmenableFunctionWindow

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor <;> norm_num
    [AmenableFunctionWindow.controlled,
      AmenableFunctionWindow.budgetControlled, sampleBudgetCertificate,
      sampleAmenableFunctionWindow]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AmenableFunctionWindow) : Bool :=
  data.all fun w => w.certificateBudgetWindow ≤ w.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAmenableFunctionWindow] = true := by
  unfold budgetCertificateListReady sampleAmenableFunctionWindow
  native_decide

example :
    budgetCertificateListReady
      [sampleAmenableFunctionWindow] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch6.IntermezzoFunctionsAmenableToSingularityAnalysis
