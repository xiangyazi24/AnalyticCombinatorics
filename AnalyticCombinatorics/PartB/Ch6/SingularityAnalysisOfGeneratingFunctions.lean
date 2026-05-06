import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Singularity analysis of generating functions
-/

namespace AnalyticCombinatorics.PartB.Ch6.SingularityAnalysisOfGeneratingFunctions

/-- Coefficients of the standard pole `(1 - z)^{-k}`. -/
def poleCoeff (k n : ℕ) : ℕ :=
  if k = 0 then 0 else (n + k - 1).choose (k - 1)

theorem poleCoeff_zero_order (n : ℕ) :
    poleCoeff 0 n = 0 := by
  simp [poleCoeff]

theorem poleCoeff_simple (n : ℕ) :
    poleCoeff 1 n = 1 := by
  simp [poleCoeff]

theorem poleCoeff_double (n : ℕ) :
    poleCoeff 2 n = n + 1 := by
  simp [poleCoeff]

/-- Transfer bound model for a singular expansion with integer inverse radius. -/
def transferEnvelope (radiusInv order n : ℕ) : ℕ :=
  poleCoeff order n * radiusInv ^ n

theorem transferEnvelope_simple (radiusInv n : ℕ) :
    transferEnvelope radiusInv 1 n = radiusInv ^ n := by
  simp [transferEnvelope, poleCoeff_simple]

def coefficientDominatedByEnvelope
    (a : ℕ → ℕ) (radiusInv order N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => a n ≤ transferEnvelope radiusInv order n

theorem geometric_dominated_by_simple_envelope :
    coefficientDominatedByEnvelope (fun n => 2 ^ n) 2 1 12 = true := by
  unfold coefficientDominatedByEnvelope transferEnvelope poleCoeff
  native_decide

structure SingularityAnalysisWindow where
  singularExpansionWindow : ℕ
  transferWindow : ℕ
  coefficientWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityAnalysisWindow.ready
    (w : SingularityAnalysisWindow) : Prop :=
  0 < w.singularExpansionWindow ∧
    w.coefficientWindow ≤ w.singularExpansionWindow + w.transferWindow + w.slack

def sampleSingularityAnalysisWindow : SingularityAnalysisWindow :=
  { singularExpansionWindow := 4
    transferWindow := 5
    coefficientWindow := 10
    slack := 1 }

example : sampleSingularityAnalysisWindow.ready := by
  norm_num [SingularityAnalysisWindow.ready, sampleSingularityAnalysisWindow]

structure SingularityAnalysisOfGeneratingFunctionsBudgetCertificate where
  singularWindow : ℕ
  transferWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityAnalysisOfGeneratingFunctionsBudgetCertificate.controlled
    (c : SingularityAnalysisOfGeneratingFunctionsBudgetCertificate) : Prop :=
  0 < c.singularWindow ∧
    c.coefficientWindow ≤ c.singularWindow + c.transferWindow + c.slack

def SingularityAnalysisOfGeneratingFunctionsBudgetCertificate.budgetControlled
    (c : SingularityAnalysisOfGeneratingFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.singularWindow + c.transferWindow + c.coefficientWindow + c.slack

def SingularityAnalysisOfGeneratingFunctionsBudgetCertificate.Ready
    (c : SingularityAnalysisOfGeneratingFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularityAnalysisOfGeneratingFunctionsBudgetCertificate.size
    (c : SingularityAnalysisOfGeneratingFunctionsBudgetCertificate) : ℕ :=
  c.singularWindow + c.transferWindow + c.coefficientWindow + c.slack

def sampleSingularityAnalysisOfGeneratingFunctionsBudgetCertificate :
    SingularityAnalysisOfGeneratingFunctionsBudgetCertificate :=
  { singularWindow := 4
    transferWindow := 5
    coefficientWindow := 10
    certificateBudgetWindow := 20
    slack := 1 }

example : sampleSingularityAnalysisOfGeneratingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [SingularityAnalysisOfGeneratingFunctionsBudgetCertificate.controlled,
        sampleSingularityAnalysisOfGeneratingFunctionsBudgetCertificate]
  · norm_num
      [SingularityAnalysisOfGeneratingFunctionsBudgetCertificate.budgetControlled,
        sampleSingularityAnalysisOfGeneratingFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleSingularityAnalysisOfGeneratingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityAnalysisOfGeneratingFunctionsBudgetCertificate.controlled,
      sampleSingularityAnalysisOfGeneratingFunctionsBudgetCertificate]
  · norm_num [SingularityAnalysisOfGeneratingFunctionsBudgetCertificate.budgetControlled,
      sampleSingularityAnalysisOfGeneratingFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularityAnalysisOfGeneratingFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityAnalysisOfGeneratingFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SingularityAnalysisOfGeneratingFunctionsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularityAnalysisOfGeneratingFunctionsBudgetCertificate] =
        true := by
  unfold budgetCertificateListReady
    sampleSingularityAnalysisOfGeneratingFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.SingularityAnalysisOfGeneratingFunctions
