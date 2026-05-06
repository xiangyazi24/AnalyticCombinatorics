import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Integer compositions and partitions
-/

namespace AnalyticCombinatorics.PartA.Ch1.IntegerCompositionsAndPartitions

/-- Number of unrestricted compositions of a positive integer. -/
def compositionCount : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ n

theorem compositionCount_zero :
    compositionCount 0 = 1 := rfl

theorem compositionCount_succ (n : ℕ) :
    compositionCount (n + 1) = 2 ^ n := rfl

theorem compositionCount_samples :
    compositionCount 1 = 1 ∧
      compositionCount 2 = 2 ∧
        compositionCount 5 = 16 := by
  native_decide

/-- Compositions of `n` into exactly `k` positive parts. -/
def compositionCountWithParts (n k : ℕ) : ℕ :=
  if k = 0 then
    if n = 0 then 1 else 0
  else if k ≤ n then (n - 1).choose (k - 1) else 0

theorem compositionCountWithParts_one_part {n : ℕ} (h : 0 < n) :
    compositionCountWithParts n 1 = 1 := by
  cases n with
  | zero => cases h
  | succ n => simp [compositionCountWithParts]

theorem compositionCountWithParts_samples :
    compositionCountWithParts 5 1 = 1 ∧
      compositionCountWithParts 5 2 = 4 ∧
        compositionCountWithParts 5 3 = 6 := by
  native_decide

/-- Partition prefix table used for finite audits. -/
def partitionCountSmall : Fin 8 → ℕ :=
  ![1, 1, 2, 3, 5, 7, 11, 15]

theorem partitionCountSmall_samples :
    partitionCountSmall 0 = 1 ∧
      partitionCountSmall 4 = 5 ∧
        partitionCountSmall 7 = 15 := by
  native_decide

example : compositionCountWithParts 6 3 = 10 := by
  unfold compositionCountWithParts
  native_decide

example : partitionCountSmall 6 = 11 := by
  native_decide

structure BudgetCertificate where
  compositionWindow : ℕ
  partitionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.compositionWindow ∧
    c.partitionWindow ≤ c.compositionWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.compositionWindow + c.partitionWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.compositionWindow + c.partitionWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { compositionWindow := 5, partitionWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

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

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.IntegerCompositionsAndPartitions
