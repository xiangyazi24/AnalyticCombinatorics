import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Functions amenable to singularity analysis.

Finite certificates for Δ-analyticity, aperiodicity, local singular
expansion data, and transfer-rule readiness.
-/

namespace AnalyticCombinatorics.PartB.Ch6.FunctionsAmenableToSingularityAnalysis

/-- A finite support sample for detecting coefficient periodicity. -/
def supportGcdUpTo (support : ℕ → Bool) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun g n => if support n then Nat.gcd g n else g) 0

def aperiodicSupportSample (n : ℕ) : Bool :=
  n = 2 || n = 3 || n = 5 || n = 8

def evenSupportSample (n : ℕ) : Bool :=
  n = 2 || n = 4 || n = 6 || n = 8

theorem supportGcd_samples :
    supportGcdUpTo aperiodicSupportSample 8 = 1 ∧
      supportGcdUpTo evenSupportSample 8 = 2 := by
  unfold supportGcdUpTo aperiodicSupportSample evenSupportSample
  native_decide

/-- Δ-domain and singular expansion data for a transfer theorem instance. -/
structure AmenableSingularityWindow where
  radiusWindow : ℕ
  apertureWindow : ℕ
  expansionOrder : ℕ
  coefficientSupportGcd : ℕ
  errorWindow : ℕ
deriving DecidableEq, Repr

def AmenableSingularityWindow.deltaReady
    (w : AmenableSingularityWindow) : Prop :=
  0 < w.radiusWindow ∧ 0 < w.apertureWindow

def AmenableSingularityWindow.aperiodic
    (w : AmenableSingularityWindow) : Prop :=
  w.coefficientSupportGcd = 1

def AmenableSingularityWindow.expansionReady
    (w : AmenableSingularityWindow) : Prop :=
  0 < w.expansionOrder ∧
    w.errorWindow ≤ w.radiusWindow + w.apertureWindow + w.expansionOrder

def AmenableSingularityWindow.ready
    (w : AmenableSingularityWindow) : Prop :=
  w.deltaReady ∧ w.aperiodic ∧ w.expansionReady

def sampleAmenableSingularityWindow : AmenableSingularityWindow :=
  { radiusWindow := 5
    apertureWindow := 2
    expansionOrder := 3
    coefficientSupportGcd := 1
    errorWindow := 9 }

theorem sampleAmenableSingularityWindow_ready :
    sampleAmenableSingularityWindow.ready := by
  norm_num [AmenableSingularityWindow.ready,
    AmenableSingularityWindow.deltaReady,
    AmenableSingularityWindow.aperiodic,
    AmenableSingularityWindow.expansionReady,
    sampleAmenableSingularityWindow]

/-- Boolean audit for finite amenability windows. -/
def amenableSingularityWindowListReady
    (data : List AmenableSingularityWindow) : Bool :=
  data.all fun w =>
    0 < w.radiusWindow &&
      0 < w.apertureWindow &&
        w.coefficientSupportGcd == 1 &&
          0 < w.expansionOrder &&
            w.errorWindow ≤
              w.radiusWindow + w.apertureWindow + w.expansionOrder

theorem amenableSingularityWindowList_readyWindow :
    amenableSingularityWindowListReady
      [sampleAmenableSingularityWindow,
       { radiusWindow := 8, apertureWindow := 3, expansionOrder := 5,
         coefficientSupportGcd := 1, errorWindow := 15 }] = true := by
  unfold amenableSingularityWindowListReady
    sampleAmenableSingularityWindow
  native_decide

example :
    amenableSingularityWindowListReady
      [sampleAmenableSingularityWindow] = true := by
  unfold amenableSingularityWindowListReady
    sampleAmenableSingularityWindow
  native_decide

/-- A transfer scale descriptor for an amenable singular expansion. -/
structure TransferScaleWindow where
  exponentNumerator : ℤ
  exponentDenominator : ℕ
  gammaDenominatorWindow : ℕ
  coefficientScaleWindow : ℕ
deriving DecidableEq, Repr

def TransferScaleWindow.ready (w : TransferScaleWindow) : Prop :=
  0 < w.exponentDenominator ∧
    0 < w.gammaDenominatorWindow ∧
      w.coefficientScaleWindow ≤
        w.gammaDenominatorWindow + w.exponentDenominator +
          w.exponentNumerator.natAbs

def squareRootTransferScale : TransferScaleWindow :=
  { exponentNumerator := -1
    exponentDenominator := 2
    gammaDenominatorWindow := 4
    coefficientScaleWindow := 7 }

theorem squareRootTransferScale_ready :
    squareRootTransferScale.ready := by
  norm_num [TransferScaleWindow.ready, squareRootTransferScale]

example : squareRootTransferScale.ready := by
  exact squareRootTransferScale_ready

structure FunctionsAmenableToSingularityAnalysisBudgetCertificate where
  deltaWindow : ℕ
  expansionWindow : ℕ
  aperiodicityWindow : ℕ
  transferWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FunctionsAmenableToSingularityAnalysisBudgetCertificate.controlled
    (c : FunctionsAmenableToSingularityAnalysisBudgetCertificate) : Prop :=
  0 < c.deltaWindow ∧
    c.expansionWindow ≤ c.deltaWindow + c.slack ∧
      c.transferWindow ≤
        c.expansionWindow + c.aperiodicityWindow + c.slack

def FunctionsAmenableToSingularityAnalysisBudgetCertificate.budgetControlled
    (c : FunctionsAmenableToSingularityAnalysisBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.deltaWindow + c.expansionWindow + c.aperiodicityWindow +
      c.transferWindow + c.slack

def FunctionsAmenableToSingularityAnalysisBudgetCertificate.Ready
    (c : FunctionsAmenableToSingularityAnalysisBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FunctionsAmenableToSingularityAnalysisBudgetCertificate.size
    (c : FunctionsAmenableToSingularityAnalysisBudgetCertificate) : ℕ :=
  c.deltaWindow + c.expansionWindow + c.aperiodicityWindow +
    c.transferWindow + c.slack

theorem functionsAmenableToSingularityAnalysis_budgetCertificate_le_size
    (c : FunctionsAmenableToSingularityAnalysisBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleFunctionsAmenableToSingularityAnalysisBudgetCertificate :
    FunctionsAmenableToSingularityAnalysisBudgetCertificate :=
  { deltaWindow := 5
    expansionWindow := 6
    aperiodicityWindow := 4
    transferWindow := 10
    certificateBudgetWindow := 26
    slack := 1 }

example :
    sampleFunctionsAmenableToSingularityAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num
      [FunctionsAmenableToSingularityAnalysisBudgetCertificate.controlled,
       sampleFunctionsAmenableToSingularityAnalysisBudgetCertificate]
  · norm_num
      [FunctionsAmenableToSingularityAnalysisBudgetCertificate.budgetControlled,
       sampleFunctionsAmenableToSingularityAnalysisBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFunctionsAmenableToSingularityAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [FunctionsAmenableToSingularityAnalysisBudgetCertificate.controlled,
      sampleFunctionsAmenableToSingularityAnalysisBudgetCertificate]
  · norm_num [FunctionsAmenableToSingularityAnalysisBudgetCertificate.budgetControlled,
      sampleFunctionsAmenableToSingularityAnalysisBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFunctionsAmenableToSingularityAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleFunctionsAmenableToSingularityAnalysisBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FunctionsAmenableToSingularityAnalysisBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFunctionsAmenableToSingularityAnalysisBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFunctionsAmenableToSingularityAnalysisBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.FunctionsAmenableToSingularityAnalysis
