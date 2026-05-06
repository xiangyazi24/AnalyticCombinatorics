import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Perspective
-/

namespace AnalyticCombinatorics.PartB.Ch4.Perspective

/-- Coarse coverage score for Chapter IV navigation. -/
def perspectiveCoverage (primary secondary : ℕ) : ℕ :=
  primary + secondary

theorem perspectiveCoverage_comm (primary secondary : ℕ) :
    perspectiveCoverage primary secondary =
      perspectiveCoverage secondary primary := by
  unfold perspectiveCoverage
  omega

/-- Balance check: the secondary topic count is within the allowed slack. -/
def perspectiveBalanced (primary secondary slack : ℕ) : Bool :=
  secondary ≤ primary + slack

theorem perspectiveBalanced_sample :
    perspectiveBalanced 2 3 1 = true := by
  native_decide

structure PerspectiveWindow where
  analyticObjects : ℕ
  singularityTransfer : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PerspectiveWindow.controlled (w : PerspectiveWindow) : Prop :=
  0 < w.analyticObjects ∧
    w.singularityTransfer ≤ w.analyticObjects + w.slack

def PerspectiveWindow.budgetControlled (w : PerspectiveWindow) : Prop :=
  w.certificateBudgetWindow ≤
    w.analyticObjects + w.singularityTransfer + w.slack

def PerspectiveWindow.Ready (w : PerspectiveWindow) : Prop :=
  w.controlled ∧ w.budgetControlled

def PerspectiveWindow.size (w : PerspectiveWindow) : ℕ :=
  w.analyticObjects + w.singularityTransfer + w.slack

def samplePerspectiveWindow : PerspectiveWindow :=
  { analyticObjects := 2
    singularityTransfer := 3
    certificateBudgetWindow := 6
    slack := 1 }

example : samplePerspectiveWindow.Ready := by
  constructor <;> norm_num
    [PerspectiveWindow.controlled, PerspectiveWindow.budgetControlled,
      samplePerspectiveWindow]

theorem samplePerspectiveWindow_ready :
    samplePerspectiveWindow.Ready := by
  constructor <;> norm_num
    [PerspectiveWindow.controlled, PerspectiveWindow.budgetControlled,
      samplePerspectiveWindow]

theorem window_budgetCertificate_le_size
    (w : PerspectiveWindow) (h : w.Ready) :
    w.certificateBudgetWindow ≤ w.size := by
  exact h.2

theorem sampleWindow_le_size :
    samplePerspectiveWindow.certificateBudgetWindow ≤
      samplePerspectiveWindow.size := by
  have h : samplePerspectiveWindow.Ready := by
    constructor <;> norm_num
      [PerspectiveWindow.controlled, PerspectiveWindow.budgetControlled,
        samplePerspectiveWindow]
  exact h.2

abbrev BudgetCertificate := PerspectiveWindow

def sampleBudgetCertificate : BudgetCertificate :=
  samplePerspectiveWindow

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  exact samplePerspectiveWindow_ready

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PerspectiveWindow) : Bool :=
  data.all fun w => w.certificateBudgetWindow ≤ w.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [samplePerspectiveWindow] = true := by
  unfold budgetCertificateListReady samplePerspectiveWindow
  native_decide

example :
    budgetCertificateListReady
      [samplePerspectiveWindow] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch4.Perspective
