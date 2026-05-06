import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Applications of rational and meromorphic asymptotics

Chapter-level finite roadmap windows for rational and meromorphic applications.
-/

namespace AnalyticCombinatorics.PartB.Ch5.ApplicationsOfRationalAndMeromorphicAsymptotics

/-- Linear recurrence model induced by a rational generating function. -/
def fibonacciLike : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacciLike (n + 1) + fibonacciLike n

theorem fibonacciLike_samples :
    fibonacciLike 2 = 1 ∧ fibonacciLike 3 = 2 ∧
      fibonacciLike 6 = 8 := by
  native_decide

/-- Transfer-matrix path count in a complete directed graph with `states` states. -/
def completeAutomatonPathCount (states length : ℕ) : ℕ :=
  states ^ length

theorem completeAutomatonPathCount_zero_length (states : ℕ) :
    completeAutomatonPathCount states 0 = 1 := by
  simp [completeAutomatonPathCount]

theorem completeAutomatonPathCount_binary_samples :
    completeAutomatonPathCount 2 3 = 8 ∧
      completeAutomatonPathCount 3 2 = 9 := by
  native_decide

/-- Meromorphic residue transfer for a simple pole. -/
def simpleResidueTransfer (residue radiusInv n : ℕ) : ℕ :=
  residue * radiusInv ^ n

theorem simpleResidueTransfer_unit (radiusInv n : ℕ) :
    simpleResidueTransfer 1 radiusInv n = radiusInv ^ n := by
  simp [simpleResidueTransfer]

structure ApplicationRoadmapWindow where
  rationalWindow : ℕ
  meromorphicWindow : ℕ
  applicationWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ApplicationRoadmapWindow.ready (w : ApplicationRoadmapWindow) : Prop :=
  0 < w.rationalWindow ∧
    w.applicationWindow ≤ w.rationalWindow + w.meromorphicWindow + w.slack

def sampleApplicationRoadmapWindow : ApplicationRoadmapWindow :=
  { rationalWindow := 5
    meromorphicWindow := 4
    applicationWindow := 10
    slack := 1 }

example : sampleApplicationRoadmapWindow.ready := by
  norm_num [ApplicationRoadmapWindow.ready, sampleApplicationRoadmapWindow]

def applicationRoadmapWindowListReady
    (data : List ApplicationRoadmapWindow) : Bool :=
  data.all fun w =>
    0 < w.rationalWindow &&
      w.applicationWindow ≤ w.rationalWindow + w.meromorphicWindow + w.slack

theorem applicationRoadmapWindowList_readyWindow :
    applicationRoadmapWindowListReady
      [sampleApplicationRoadmapWindow,
       { rationalWindow := 3, meromorphicWindow := 2,
         applicationWindow := 5, slack := 0 }] = true := by
  unfold applicationRoadmapWindowListReady sampleApplicationRoadmapWindow
  native_decide

structure ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate where
  rationalWindow : ℕ
  meromorphicWindow : ℕ
  applicationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate.controlled
    (c : ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate) :
    Prop :=
  0 < c.rationalWindow ∧
    c.applicationWindow ≤ c.rationalWindow + c.meromorphicWindow + c.slack

def ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate.budgetControlled
    (c : ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate) :
    Prop :=
  c.certificateBudgetWindow ≤
    c.rationalWindow + c.meromorphicWindow + c.applicationWindow + c.slack

def ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate.Ready
    (c : ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate) :
    Prop :=
  c.controlled ∧ c.budgetControlled

def ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate.size
    (c : ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate) :
    ℕ :=
  c.rationalWindow + c.meromorphicWindow + c.applicationWindow + c.slack

def sampleApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate :
    ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate :=
  { rationalWindow := 5
    meromorphicWindow := 4
    applicationWindow := 10
    certificateBudgetWindow := 20
    slack := 1 }

example :
    ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate.Ready
      sampleApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate := by
  constructor
  · norm_num
      [ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate.controlled,
        sampleApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate]
  · norm_num
      [ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate.budgetControlled,
        sampleApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate.controlled,
      sampleApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate]
  · norm_num [ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate.budgetControlled,
      sampleApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data :
      List ApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate] =
        true := by
  unfold budgetCertificateListReady
    sampleApplicationsOfRationalAndMeromorphicAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.ApplicationsOfRationalAndMeromorphicAsymptotics
