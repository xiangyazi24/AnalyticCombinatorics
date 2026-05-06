import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Method of steepest descent
-/

namespace AnalyticCombinatorics.Asymptotics.SteepestDescentMethod

/-- Discrete height drop from a saddle along a descent contour. -/
def descentDrop (saddle n : ℕ) : ℕ :=
  if n ≤ saddle then saddle - n else n - saddle

theorem descentDrop_saddle (saddle : ℕ) :
    descentDrop saddle saddle = 0 := by
  simp [descentDrop]

theorem descentDrop_right (saddle d : ℕ) :
    descentDrop saddle (saddle + d) = d := by
  by_cases hd : d = 0
  · simp [descentDrop, hd]
  · have hlt : saddle < saddle + d :=
      Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hd)
    have hnle : ¬ saddle + d ≤ saddle := not_le_of_gt hlt
    simp [descentDrop, hnle]

/-- Descent contour audit on a sampled right ray. -/
def descentRayCheck (saddle radius : ℕ) : Bool :=
  (List.range (radius + 1)).all fun d =>
    descentDrop saddle (saddle + d) = d

theorem descentRayCheck_sample :
    descentRayCheck 5 8 = true := by
  unfold descentRayCheck descentDrop
  native_decide

/-- Cleared Gaussian envelope around a saddle. -/
def descentGaussianEnvelope (height saddle n : ℕ) : ℕ :=
  height + descentDrop saddle n ^ 2

theorem descentGaussianEnvelope_at_saddle (height saddle : ℕ) :
    descentGaussianEnvelope height saddle saddle = height := by
  simp [descentGaussianEnvelope, descentDrop_saddle]

structure DescentContourWindow where
  saddleWindow : ℕ
  descentWindow : ℕ
  tailWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DescentContourWindow.ready (w : DescentContourWindow) : Prop :=
  0 < w.saddleWindow ∧
    w.tailWindow ≤ w.saddleWindow + w.descentWindow + w.slack

def sampleDescentContourWindow : DescentContourWindow :=
  { saddleWindow := 4, descentWindow := 3, tailWindow := 7, slack := 0 }

example : sampleDescentContourWindow.ready := by
  norm_num [DescentContourWindow.ready, sampleDescentContourWindow]

structure BudgetCertificate where
  saddleWindow : ℕ
  descentWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.saddleWindow ∧ c.descentWindow ≤ c.saddleWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.saddleWindow + c.descentWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.saddleWindow + c.descentWindow + c.slack

theorem steepestDescentMethod_budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { saddleWindow := 5, descentWindow := 6, certificateBudgetWindow := 12,
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

end AnalyticCombinatorics.Asymptotics.SteepestDescentMethod
