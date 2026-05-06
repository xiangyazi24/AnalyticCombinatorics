import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Stationary phase method
-/

namespace AnalyticCombinatorics.Asymptotics.StationaryPhaseMethod

/-- Discrete phase curvature around a stationary point. -/
def phaseQuadratic (center curvature n : ℕ) : ℕ :=
  curvature * (if n ≤ center then (center - n) ^ 2 else (n - center) ^ 2)

theorem phaseQuadratic_center (center curvature : ℕ) :
    phaseQuadratic center curvature center = 0 := by
  simp [phaseQuadratic]

theorem phaseQuadratic_right (center curvature d : ℕ) :
    phaseQuadratic center curvature (center + d) = curvature * d ^ 2 := by
  by_cases hd : d = 0
  · simp [phaseQuadratic, hd]
  · have hlt : center < center + d :=
      Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hd)
    have hnle : ¬ center + d ≤ center := not_le_of_gt hlt
    simp [phaseQuadratic, hnle]

def stationaryPhaseWindowCheck (center curvature radius : ℕ) : Bool :=
  (List.range (radius + 1)).all fun d =>
    phaseQuadratic center curvature (center + d) = curvature * d ^ 2

theorem stationaryPhaseWindowCheck_sample :
    stationaryPhaseWindowCheck 4 3 6 = true := by
  unfold stationaryPhaseWindowCheck phaseQuadratic
  native_decide

/-- Oscillation budget increasing with curvature and sample width. -/
def oscillationBudget (curvature radius : ℕ) : ℕ :=
  curvature * (radius + 1)

theorem oscillationBudget_pos {curvature : ℕ} (h : 0 < curvature) (radius : ℕ) :
    0 < oscillationBudget curvature radius := by
  unfold oscillationBudget
  exact Nat.mul_pos h (Nat.succ_pos radius)

structure PhaseWindow where
  stationaryWindow : ℕ
  curvatureWindow : ℕ
  oscillationWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PhaseWindow.ready (w : PhaseWindow) : Prop :=
  0 < w.stationaryWindow ∧
    w.oscillationWindow ≤ w.stationaryWindow + w.curvatureWindow + w.slack

def samplePhaseWindow : PhaseWindow :=
  { stationaryWindow := 4, curvatureWindow := 3,
    oscillationWindow := 7, slack := 0 }

example : samplePhaseWindow.ready := by
  norm_num [PhaseWindow.ready, samplePhaseWindow]

structure BudgetCertificate where
  stationaryWindow : ℕ
  curvatureWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.stationaryWindow ∧ c.curvatureWindow ≤ c.stationaryWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.stationaryWindow + c.curvatureWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.stationaryWindow + c.curvatureWindow + c.slack

theorem stationaryPhaseMethod_budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { stationaryWindow := 5, curvatureWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

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

end AnalyticCombinatorics.Asymptotics.StationaryPhaseMethod
