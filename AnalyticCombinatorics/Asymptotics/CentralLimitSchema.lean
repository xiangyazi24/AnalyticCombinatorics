import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Central limit schema
-/

namespace AnalyticCombinatorics.Asymptotics.CentralLimitSchema

/-- Finite first moment for a distribution on `0, ..., N`. -/
def finiteMean (mass : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun total (k : ℕ) => total + (k : ℚ) * mass k) 0

/-- Finite second raw moment. -/
def finiteSecondMoment (mass : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun total (k : ℕ) => total + (k : ℚ) ^ 2 * mass k) 0

def bernoulliHalf : ℕ → ℚ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | _ => 0

theorem bernoulliHalf_mean :
    finiteMean bernoulliHalf 4 = 1 / 2 := by
  unfold finiteMean bernoulliHalf
  native_decide

theorem bernoulliHalf_secondMoment :
    finiteSecondMoment bernoulliHalf 4 = 1 / 2 := by
  unfold finiteSecondMoment bernoulliHalf
  native_decide

/-- Finite quasi-power normalization audit at `t = 0`. -/
def mgfNormalizedAtZero (mgf : ℕ → ℚ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => mgf n 0 = 1

theorem constantMgf_normalized :
    mgfNormalizedAtZero (fun _ _ => 1) 12 = true := by
  unfold mgfNormalizedAtZero
  native_decide

structure CentralLimitWindow where
  meanWindow : ℕ
  varianceWindow : ℕ
  normalizationWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CentralLimitWindow.ready (w : CentralLimitWindow) : Prop :=
  0 < w.varianceWindow ∧
    w.normalizationWindow ≤ w.meanWindow + w.varianceWindow + w.slack

def sampleCentralLimitWindow : CentralLimitWindow :=
  { meanWindow := 4, varianceWindow := 3,
    normalizationWindow := 7, slack := 0 }

example : sampleCentralLimitWindow.ready := by
  norm_num [CentralLimitWindow.ready, sampleCentralLimitWindow]

structure BudgetCertificate where
  varianceWindow : ℕ
  normalWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.varianceWindow ∧ c.normalWindow ≤ c.varianceWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.varianceWindow + c.normalWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.varianceWindow + c.normalWindow + c.slack

theorem centralLimitSchema_budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { varianceWindow := 5, normalWindow := 6, certificateBudgetWindow := 12,
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.CentralLimitSchema
