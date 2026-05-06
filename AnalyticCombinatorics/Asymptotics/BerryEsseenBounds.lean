import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Berry-Esseen bounds
-/

namespace AnalyticCombinatorics.Asymptotics.BerryEsseenBounds

/-- Third absolute moment over a finite support. -/
def thirdMomentProxy (mass : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun total (k : ℕ) => total + (k : ℚ) ^ 3 * mass k) 0

def symmetricTwoPoint : ℕ → ℚ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | _ => 0

theorem symmetricTwoPoint_thirdMoment :
    thirdMomentProxy symmetricTwoPoint 4 = 1 / 2 := by
  unfold thirdMomentProxy symmetricTwoPoint
  native_decide

/-- Cleared-denominator Berry-Esseen error budget. -/
def berryEsseenErrorBudget
    (thirdMoment variance sampleSize constant : ℕ) : ℕ :=
  constant * thirdMoment * (sampleSize + 1) / (variance + 1)

theorem berryEsseenErrorBudget_zero_moment
    (variance sampleSize constant : ℕ) :
    berryEsseenErrorBudget 0 variance sampleSize constant = 0 := by
  simp [berryEsseenErrorBudget]

def berryEsseenBudgetCheck
    (thirdMoment variance sampleSize constant bound : ℕ) : Bool :=
  berryEsseenErrorBudget thirdMoment variance sampleSize constant ≤ bound

theorem berryEsseenBudgetCheck_sample :
    berryEsseenBudgetCheck 2 3 5 1 3 = true := by
  unfold berryEsseenBudgetCheck berryEsseenErrorBudget
  native_decide

structure BerryEsseenWindow where
  thirdMomentWindow : ℕ
  varianceWindow : ℕ
  errorWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BerryEsseenWindow.ready (w : BerryEsseenWindow) : Prop :=
  0 < w.varianceWindow ∧
    w.errorWindow ≤ w.thirdMomentWindow + w.varianceWindow + w.slack

def sampleBerryEsseenWindow : BerryEsseenWindow :=
  { thirdMomentWindow := 4, varianceWindow := 3, errorWindow := 7, slack := 0 }

example : sampleBerryEsseenWindow.ready := by
  norm_num [BerryEsseenWindow.ready, sampleBerryEsseenWindow]

structure BudgetCertificate where
  momentWindow : ℕ
  errorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.momentWindow ∧ c.errorWindow ≤ c.momentWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.momentWindow + c.errorWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.momentWindow + c.errorWindow + c.slack

theorem berryEsseenBounds_budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { momentWindow := 5, errorWindow := 6, certificateBudgetWindow := 12,
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

end AnalyticCombinatorics.Asymptotics.BerryEsseenBounds
