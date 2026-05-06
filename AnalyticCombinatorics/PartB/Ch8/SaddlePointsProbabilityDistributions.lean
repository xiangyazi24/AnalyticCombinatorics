import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Saddle points and probability distributions.
-/

namespace AnalyticCombinatorics.PartB.Ch8.SaddlePointsProbabilityDistributions

/-- Finite moment descriptor generated from a saddle-point approximation. -/
structure SaddleMomentWindow where
  meanNumerator : ℤ
  varianceNumerator : ℕ
  scaleDenominator : ℕ
deriving DecidableEq, Repr

def SaddleMomentWindow.valid (w : SaddleMomentWindow) : Prop :=
  0 < w.scaleDenominator ∧ 0 < w.varianceNumerator

/-- Discrete Gaussian-like mass model around an integer center. -/
def centeredMassProxy (center radius n : ℕ) : ℕ :=
  if n ≤ center + radius ∧ center ≤ n + radius then radius + 1 else 0

/-- Finite support check for a saddle-derived probability model. -/
def centeredMassSupportCheck (center radius N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    centeredMassProxy center radius n ≤ radius + 1

def SaddleDistributionWindow (w : SaddleMomentWindow) (center radius N : ℕ) : Prop :=
  w.valid ∧ centeredMassSupportCheck center radius N = true

theorem centeredMassSupport_window :
    SaddleDistributionWindow
      { meanNumerator := 0, varianceNumerator := 1, scaleDenominator := 1 }
      5 3 12 := by
  constructor
  · norm_num [SaddleMomentWindow.valid]
  · unfold centeredMassSupportCheck centeredMassProxy
    native_decide

/-- Prefix mass of the centered saddle model. -/
def centeredMassPrefix (center radius N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total n => total + centeredMassProxy center radius n) 0

def CenteredMassPrefixWindow (center radius N total : ℕ) : Prop :=
  centeredMassPrefix center radius N = total

theorem centeredMass_prefixWindow :
    CenteredMassPrefixWindow 5 3 12 28 := by
  unfold CenteredMassPrefixWindow centeredMassPrefix centeredMassProxy
  native_decide

example : centeredMassProxy 5 3 2 = 4 := by
  unfold centeredMassProxy
  native_decide

example : centeredMassPrefix 5 1 6 = 6 := by
  unfold centeredMassPrefix centeredMassProxy
  native_decide

structure SaddlePointsProbabilityDistributionsBudgetCertificate where
  saddleWindow : ℕ
  momentWindow : ℕ
  distributionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddlePointsProbabilityDistributionsBudgetCertificate.controlled
    (c : SaddlePointsProbabilityDistributionsBudgetCertificate) : Prop :=
  0 < c.saddleWindow ∧
    c.distributionWindow ≤ c.saddleWindow + c.momentWindow + c.slack

def SaddlePointsProbabilityDistributionsBudgetCertificate.budgetControlled
    (c : SaddlePointsProbabilityDistributionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleWindow + c.momentWindow + c.distributionWindow + c.slack

def SaddlePointsProbabilityDistributionsBudgetCertificate.Ready
    (c : SaddlePointsProbabilityDistributionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SaddlePointsProbabilityDistributionsBudgetCertificate.size
    (c : SaddlePointsProbabilityDistributionsBudgetCertificate) : ℕ :=
  c.saddleWindow + c.momentWindow + c.distributionWindow + c.slack

theorem saddlePointsProbabilityDistributions_budgetCertificate_le_size
    (c : SaddlePointsProbabilityDistributionsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSaddlePointsProbabilityDistributionsBudgetCertificate :
    SaddlePointsProbabilityDistributionsBudgetCertificate :=
  { saddleWindow := 5
    momentWindow := 6
    distributionWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSaddlePointsProbabilityDistributionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddlePointsProbabilityDistributionsBudgetCertificate.controlled,
      sampleSaddlePointsProbabilityDistributionsBudgetCertificate]
  · norm_num [SaddlePointsProbabilityDistributionsBudgetCertificate.budgetControlled,
      sampleSaddlePointsProbabilityDistributionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddlePointsProbabilityDistributionsBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddlePointsProbabilityDistributionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSaddlePointsProbabilityDistributionsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [SaddlePointsProbabilityDistributionsBudgetCertificate.controlled,
        sampleSaddlePointsProbabilityDistributionsBudgetCertificate]
  · norm_num
      [SaddlePointsProbabilityDistributionsBudgetCertificate.budgetControlled,
        sampleSaddlePointsProbabilityDistributionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List SaddlePointsProbabilityDistributionsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSaddlePointsProbabilityDistributionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSaddlePointsProbabilityDistributionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.SaddlePointsProbabilityDistributions
