import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite partition and composition helpers.

The definitions here model small additive decompositions used in symbolic
constructions and coefficient recurrences.
-/

namespace AnalyticCombinatorics.AppA.FinitePartitions

def weakCompositionsTwo (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (n + 1)).map (fun k => (k, n - k))

def pairSumsTo (n : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 + p.2 = n

def pairWeight (p : ℕ × ℕ) : ℕ :=
  p.1 + p.2

theorem weakCompositionsTwo_length (n : ℕ) :
    (weakCompositionsTwo n).length = n + 1 := by
  simp [weakCompositionsTwo]

theorem pairSumsTo_mk {n k : ℕ}
    (h : k ≤ n) :
    pairSumsTo n (k, n - k) := by
  unfold pairSumsTo
  omega

theorem pairWeight_eq_of_pairSumsTo {n : ℕ} {p : ℕ × ℕ}
    (h : pairSumsTo n p) :
    pairWeight p = n := by
  simpa [pairWeight, pairSumsTo] using h

def integerPartitionCounts : Fin 11 → ℕ :=
  ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42]

theorem integerPartitionCounts_prefix_monotone :
    ∀ i : Fin 10,
      integerPartitionCounts i.castSucc ≤ integerPartitionCounts ⟨i.val + 1, by omega⟩ := by
  native_decide

theorem partition_counts_small_values :
    integerPartitionCounts 5 = 7 ∧ integerPartitionCounts 8 = 22 ∧
      integerPartitionCounts 10 = 42 := by
  native_decide

example : weakCompositionsTwo 3 = [(0, 3), (1, 2), (2, 1), (3, 0)] := by
  native_decide

example : pairSumsTo 5 (2, 3) := by
  norm_num [pairSumsTo]


structure FinitePartitionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FinitePartitionsBudgetCertificate.controlled
    (c : FinitePartitionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FinitePartitionsBudgetCertificate.budgetControlled
    (c : FinitePartitionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FinitePartitionsBudgetCertificate.Ready
    (c : FinitePartitionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FinitePartitionsBudgetCertificate.size
    (c : FinitePartitionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finitePartitions_budgetCertificate_le_size
    (c : FinitePartitionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFinitePartitionsBudgetCertificate :
    FinitePartitionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFinitePartitionsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePartitionsBudgetCertificate.controlled,
      sampleFinitePartitionsBudgetCertificate]
  · norm_num [FinitePartitionsBudgetCertificate.budgetControlled,
      sampleFinitePartitionsBudgetCertificate]

example :
    sampleFinitePartitionsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePartitionsBudgetCertificate.size := by
  apply finitePartitions_budgetCertificate_le_size
  constructor
  · norm_num [FinitePartitionsBudgetCertificate.controlled,
      sampleFinitePartitionsBudgetCertificate]
  · norm_num [FinitePartitionsBudgetCertificate.budgetControlled,
      sampleFinitePartitionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFinitePartitionsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePartitionsBudgetCertificate.controlled,
      sampleFinitePartitionsBudgetCertificate]
  · norm_num [FinitePartitionsBudgetCertificate.budgetControlled,
      sampleFinitePartitionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFinitePartitionsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePartitionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FinitePartitionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFinitePartitionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFinitePartitionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FinitePartitions
