import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Alignments, permutations, and related structures
-/

namespace AnalyticCombinatorics.PartA.Ch2.AlignmentsPermutationsAndRelatedStructures

/-- Permutation count on `n` labelled atoms. -/
def permutationCount (n : ℕ) : ℕ :=
  Nat.factorial n

theorem permutationCount_zero :
    permutationCount 0 = 1 := by
  simp [permutationCount]

theorem permutationCount_succ (n : ℕ) :
    permutationCount (n + 1) = (n + 1) * permutationCount n := by
  simp [permutationCount, Nat.factorial_succ]

/-- Alignment model: ordered lists of labelled nonempty blocks. -/
def alignmentCountSmall : Fin 6 → ℕ :=
  ![1, 1, 3, 13, 75, 541]

theorem alignmentCountSmall_samples :
    alignmentCountSmall 3 = 13 ∧ alignmentCountSmall 5 = 541 := by
  native_decide

/-- Derangement table for the first sizes. -/
def derangementSmall : Fin 7 → ℕ :=
  ![1, 0, 1, 2, 9, 44, 265]

theorem derangementSmall_samples :
    derangementSmall 4 = 9 ∧ derangementSmall 6 = 265 := by
  native_decide

structure BudgetCertificate where
  alignmentWindow : ℕ
  permutationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.alignmentWindow ∧
    c.permutationWindow ≤ c.alignmentWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.alignmentWindow + c.permutationWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.alignmentWindow + c.permutationWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { alignmentWindow := 5, permutationWindow := 6,
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

example :
    budgetCertificateListReady
      [sampleBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartA.Ch2.AlignmentsPermutationsAndRelatedStructures
