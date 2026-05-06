import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Surjections, set partitions, and words
-/

namespace AnalyticCombinatorics.PartA.Ch2.SurjectionsSetPartitionsAndWords

/-- Small Stirling numbers of the second kind, used as set-partition data. -/
def stirlingSecondSmall : Fin 6 → Fin 6 → ℕ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 1
  | ⟨2, _⟩, ⟨1, _⟩ => 1
  | ⟨2, _⟩, ⟨2, _⟩ => 1
  | ⟨3, _⟩, ⟨1, _⟩ => 1
  | ⟨3, _⟩, ⟨2, _⟩ => 3
  | ⟨3, _⟩, ⟨3, _⟩ => 1
  | ⟨4, _⟩, ⟨1, _⟩ => 1
  | ⟨4, _⟩, ⟨2, _⟩ => 7
  | ⟨4, _⟩, ⟨3, _⟩ => 6
  | ⟨4, _⟩, ⟨4, _⟩ => 1
  | _, _ => 0

theorem stirlingSecondSmall_samples :
    stirlingSecondSmall 4 2 = 7 ∧
      stirlingSecondSmall 4 3 = 6 := by
  native_decide

/-- Surjections from an `n`-set to a `k`-set: `k! S(n,k)`. -/
def surjectionCountSmall (n k : Fin 6) : ℕ :=
  Nat.factorial k.val * stirlingSecondSmall n k

theorem surjectionCountSmall_samples :
    surjectionCountSmall 4 2 = 14 ∧
      surjectionCountSmall 4 3 = 36 := by
  native_decide

def wordCount (alphabet n : ℕ) : ℕ :=
  alphabet ^ n

theorem wordCount_binary_four :
    wordCount 2 4 = 16 := by
  native_decide

structure BudgetCertificate where
  surjectionWindow : ℕ
  partitionWindow : ℕ
  wordWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.surjectionWindow ∧
    c.wordWindow ≤ c.surjectionWindow + c.partitionWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.surjectionWindow + c.partitionWindow + c.wordWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.surjectionWindow + c.partitionWindow + c.wordWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { surjectionWindow := 5, partitionWindow := 4, wordWindow := 10,
    certificateBudgetWindow := 20, slack := 1 }

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

end AnalyticCombinatorics.PartA.Ch2.SurjectionsSetPartitionsAndWords
