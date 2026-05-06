import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Landscapes of analytic functions and saddle-points
-/

namespace AnalyticCombinatorics.PartB.Ch8.LandscapesOfAnalyticFunctionsAndSaddlePoints

/-- Finite height profile for an analytic landscape near a saddle point. -/
structure LandscapeProfile where
  saddleHeight : ℕ
  boundaryHeight : ℕ
  descentSlack : ℕ
deriving DecidableEq, Repr

def LandscapeProfile.hasDescent (p : LandscapeProfile) : Prop :=
  p.boundaryHeight + p.descentSlack ≤ p.saddleHeight

theorem landscapeProfile_sample_descent :
    ({ saddleHeight := 10, boundaryHeight := 7,
       descentSlack := 3 } : LandscapeProfile).hasDescent := by
  norm_num [LandscapeProfile.hasDescent]

/-- Cleared descent gap between saddle and boundary heights. -/
def landscapeDescentGap (saddleHeight boundaryHeight : ℕ) : ℕ :=
  saddleHeight - boundaryHeight

theorem landscapeDescentGap_sample :
    landscapeDescentGap 10 7 = 3 := by
  native_decide

structure AnalyticLandscapeWindow where
  landscapeWindow : ℕ
  saddleWindow : ℕ
  descentWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticLandscapeWindow.ready (w : AnalyticLandscapeWindow) : Prop :=
  0 < w.landscapeWindow ∧
    w.descentWindow ≤ w.landscapeWindow + w.saddleWindow + w.slack

def sampleAnalyticLandscapeWindow : AnalyticLandscapeWindow :=
  { landscapeWindow := 4, saddleWindow := 3, descentWindow := 7, slack := 0 }

example : sampleAnalyticLandscapeWindow.ready := by
  norm_num [AnalyticLandscapeWindow.ready, sampleAnalyticLandscapeWindow]

structure BudgetCertificate where
  landscapeWindow : ℕ
  saddleWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.landscapeWindow ∧ c.saddleWindow ≤ c.landscapeWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.landscapeWindow + c.saddleWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.landscapeWindow + c.saddleWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { landscapeWindow := 5, saddleWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  have h : sampleBudgetCertificate.Ready := by
    constructor
    · norm_num [BudgetCertificate.controlled,
        sampleBudgetCertificate]
    · norm_num [BudgetCertificate.budgetControlled,
        sampleBudgetCertificate]
  exact h.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.LandscapesOfAnalyticFunctionsAndSaddlePoints
