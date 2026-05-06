import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Permutation run statistics.
-/

namespace AnalyticCombinatorics.PartA.Ch3.PermutationRuns

structure RunWindow where
  permutationSize : ℕ
  runCount : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def runCountTable : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 24
  | 5 => 120
  | 6 => 720
  | _ => 0

def runWindowControlled (n r : ℕ) : Prop :=
  r ≤ n + runCountTable n

def runWindowReady (w : RunWindow) : Prop :=
  0 < w.permutationSize ∧ runWindowControlled w.permutationSize w.runCount

def runWindowBudget (w : RunWindow) : ℕ :=
  w.permutationSize + w.runCount + w.slack

def increasingRunUpperBound (n : ℕ) : ℕ :=
  n

theorem runWindowReady.certificate {w : RunWindow}
    (h : runWindowReady w) :
    0 < w.permutationSize ∧ runWindowControlled w.permutationSize w.runCount ∧
      w.runCount ≤ runWindowBudget w := by
  rcases h with ⟨hsize, hcontrolled⟩
  refine ⟨hsize, hcontrolled, ?_⟩
  unfold runWindowBudget
  omega

def sampleRunWindow : RunWindow :=
  { permutationSize := 5, runCount := 12, slack := 3 }

example : runCountTable 5 = 120 := by native_decide
example : increasingRunUpperBound 5 = 5 := by native_decide
example : runWindowReady sampleRunWindow := by
  unfold runWindowReady
  constructor
  · norm_num [sampleRunWindow]
  · have htable : runCountTable 5 = 120 := by
      native_decide
    unfold runWindowControlled
    dsimp [sampleRunWindow]
    rw [htable]
    norm_num
example : runWindowBudget sampleRunWindow = 20 := by native_decide

theorem runWindowControlled_sample :
    runWindowControlled 5 12 := by
  norm_num [runWindowControlled, runCountTable]


structure PermutationRunsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PermutationRunsBudgetCertificate.controlled
    (c : PermutationRunsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PermutationRunsBudgetCertificate.budgetControlled
    (c : PermutationRunsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PermutationRunsBudgetCertificate.Ready
    (c : PermutationRunsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PermutationRunsBudgetCertificate.size
    (c : PermutationRunsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem permutationRuns_budgetCertificate_le_size
    (c : PermutationRunsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePermutationRunsBudgetCertificate :
    PermutationRunsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePermutationRunsBudgetCertificate.Ready := by
  constructor
  · norm_num [PermutationRunsBudgetCertificate.controlled,
      samplePermutationRunsBudgetCertificate]
  · norm_num [PermutationRunsBudgetCertificate.budgetControlled,
      samplePermutationRunsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePermutationRunsBudgetCertificate.certificateBudgetWindow ≤
      samplePermutationRunsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePermutationRunsBudgetCertificate.Ready := by
  constructor
  · norm_num [PermutationRunsBudgetCertificate.controlled,
      samplePermutationRunsBudgetCertificate]
  · norm_num [PermutationRunsBudgetCertificate.budgetControlled,
      samplePermutationRunsBudgetCertificate]

example :
    samplePermutationRunsBudgetCertificate.certificateBudgetWindow ≤
      samplePermutationRunsBudgetCertificate.size := by
  apply permutationRuns_budgetCertificate_le_size
  constructor
  · norm_num [PermutationRunsBudgetCertificate.controlled,
      samplePermutationRunsBudgetCertificate]
  · norm_num [PermutationRunsBudgetCertificate.budgetControlled,
      samplePermutationRunsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PermutationRunsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePermutationRunsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePermutationRunsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.PermutationRuns
