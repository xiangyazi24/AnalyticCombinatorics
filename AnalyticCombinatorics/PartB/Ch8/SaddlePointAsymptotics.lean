import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Saddle-point asymptotics
-/

namespace AnalyticCombinatorics.PartB.Ch8.SaddlePointAsymptotics

/-- Discrete saddle weight centered at a sampled saddle index. -/
def saddleQuadraticDrop (center n : ℕ) : ℕ :=
  if n ≤ center then (center - n) ^ 2 else (n - center) ^ 2

theorem saddleQuadraticDrop_center (center : ℕ) :
    saddleQuadraticDrop center center = 0 := by
  simp [saddleQuadraticDrop]

theorem saddleQuadraticDrop_right (center d : ℕ) :
    saddleQuadraticDrop center (center + d) = d ^ 2 := by
  by_cases hd : d = 0
  · simp [saddleQuadraticDrop, hd]
  · have hlt : center < center + d := Nat.lt_add_of_pos_right
      (Nat.pos_of_ne_zero hd)
    have hnle : ¬ center + d ≤ center := not_le_of_gt hlt
    simp [saddleQuadraticDrop, hnle]

/-- Finite Gaussian-like envelope around the saddle. -/
def saddleEnvelope (center height n : ℕ) : ℕ :=
  height + saddleQuadraticDrop center n

theorem saddleEnvelope_at_center (center height : ℕ) :
    saddleEnvelope center height center = height := by
  simp [saddleEnvelope, saddleQuadraticDrop_center]

def saddleWindowCheck (center radius : ℕ) : Bool :=
  (List.range (radius + 1)).all fun d =>
    saddleQuadraticDrop center (center + d) = d ^ 2

theorem saddleWindowCheck_sample :
    saddleWindowCheck 6 8 = true := by
  unfold saddleWindowCheck saddleQuadraticDrop
  native_decide

structure SaddleAsymptoticWindow where
  saddleWindow : ℕ
  contourWindow : ℕ
  coefficientWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleAsymptoticWindow.ready (w : SaddleAsymptoticWindow) : Prop :=
  0 < w.saddleWindow ∧
    w.coefficientWindow ≤ w.saddleWindow + w.contourWindow + w.slack

def sampleSaddleAsymptoticWindow : SaddleAsymptoticWindow :=
  { saddleWindow := 5, contourWindow := 4,
    coefficientWindow := 10, slack := 1 }

example : sampleSaddleAsymptoticWindow.ready := by
  norm_num [SaddleAsymptoticWindow.ready, sampleSaddleAsymptoticWindow]

structure BudgetCertificate where
  saddleWindow : ℕ
  contourWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.saddleWindow ∧ c.contourWindow ≤ c.saddleWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.saddleWindow + c.contourWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.saddleWindow + c.contourWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { saddleWindow := 5, contourWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.SaddlePointAsymptotics
