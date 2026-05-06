import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Singularity analysis and probability distributions.

Finite distribution-window bookkeeping for probability laws derived from
singular expansions.
-/

namespace AnalyticCombinatorics.PartB.Ch7.SingularityAnalysisProbabilityDistributions

/-- Probability mass model derived from normalized singular coefficients. -/
def normalizedTwoPointMass : ℕ → ℚ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | _ => 0

def probabilityMassPrefix (mass : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl (fun (total : ℚ) (n : ℕ) => total + mass n) 0

def firstMomentPrefix (mass : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun (total : ℚ) (n : ℕ) => total + (n : ℚ) * mass n) 0

theorem normalizedTwoPointMass_window :
    probabilityMassPrefix normalizedTwoPointMass 1 = 1 ∧
    firstMomentPrefix normalizedTwoPointMass 1 = 1 / 2 := by
  unfold probabilityMassPrefix firstMomentPrefix normalizedTwoPointMass
  native_decide

structure SingularityProbabilityWindow where
  singularExpansionWindow : ℕ
  momentWindow : ℕ
  distributionWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def singularityProbabilityReady
    (w : SingularityProbabilityWindow) : Prop :=
  0 < w.singularExpansionWindow ∧
    w.distributionWindow ≤
      w.singularExpansionWindow + w.momentWindow + w.slack

def singularityProbabilityBudget
    (w : SingularityProbabilityWindow) : ℕ :=
  w.singularExpansionWindow + w.momentWindow + w.distributionWindow + w.slack

theorem distributionWindow_le_singularityProbabilityBudget
    (w : SingularityProbabilityWindow) :
    w.distributionWindow ≤ singularityProbabilityBudget w := by
  unfold singularityProbabilityBudget
  omega

def sampleSingularityProbabilityWindow : SingularityProbabilityWindow :=
  { singularExpansionWindow := 5
    momentWindow := 6
    distributionWindow := 10
    slack := 1 }

example : singularityProbabilityReady sampleSingularityProbabilityWindow := by
  norm_num [singularityProbabilityReady, sampleSingularityProbabilityWindow]

structure SingularityAnalysisProbabilityDistributionsBudgetCertificate where
  expansionWindow : ℕ
  momentWindow : ℕ
  distributionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityAnalysisProbabilityDistributionsBudgetCertificate.controlled
    (c : SingularityAnalysisProbabilityDistributionsBudgetCertificate) :
    Prop :=
  0 < c.expansionWindow ∧
    c.distributionWindow ≤ c.expansionWindow + c.momentWindow + c.slack

def SingularityAnalysisProbabilityDistributionsBudgetCertificate.budgetControlled
    (c : SingularityAnalysisProbabilityDistributionsBudgetCertificate) :
    Prop :=
  c.certificateBudgetWindow ≤
    c.expansionWindow + c.momentWindow + c.distributionWindow + c.slack

def SingularityAnalysisProbabilityDistributionsBudgetCertificate.Ready
    (c : SingularityAnalysisProbabilityDistributionsBudgetCertificate) :
    Prop :=
  c.controlled ∧ c.budgetControlled

def SingularityAnalysisProbabilityDistributionsBudgetCertificate.size
    (c : SingularityAnalysisProbabilityDistributionsBudgetCertificate) : ℕ :=
  c.expansionWindow + c.momentWindow + c.distributionWindow + c.slack

theorem singularityAnalysisProbabilityDistributions_budgetCertificate_le_size
    (c : SingularityAnalysisProbabilityDistributionsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSingularityAnalysisProbabilityDistributionsBudgetCertificate :
    SingularityAnalysisProbabilityDistributionsBudgetCertificate :=
  { expansionWindow := 5
    momentWindow := 6
    distributionWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example :
    sampleSingularityAnalysisProbabilityDistributionsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [SingularityAnalysisProbabilityDistributionsBudgetCertificate.controlled,
        sampleSingularityAnalysisProbabilityDistributionsBudgetCertificate]
  · norm_num
      [SingularityAnalysisProbabilityDistributionsBudgetCertificate.budgetControlled,
        sampleSingularityAnalysisProbabilityDistributionsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleSingularityAnalysisProbabilityDistributionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityAnalysisProbabilityDistributionsBudgetCertificate.controlled,
      sampleSingularityAnalysisProbabilityDistributionsBudgetCertificate]
  · norm_num [SingularityAnalysisProbabilityDistributionsBudgetCertificate.budgetControlled,
      sampleSingularityAnalysisProbabilityDistributionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularityAnalysisProbabilityDistributionsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityAnalysisProbabilityDistributionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List SingularityAnalysisProbabilityDistributionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularityAnalysisProbabilityDistributionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSingularityAnalysisProbabilityDistributionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.SingularityAnalysisProbabilityDistributions
