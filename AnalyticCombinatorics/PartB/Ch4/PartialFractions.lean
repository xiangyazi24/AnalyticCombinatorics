import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.PartialFractions


/-!
Finite coefficient checks for several rational generating functions obtained from
partial fraction decompositions.
-/

def oneTwoCoeff (n : ℕ) : ℕ :=
  2 ^ (n + 1) - 1

def oneTwoTable : Fin 11 → ℕ :=
  ![1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047]

theorem oneTwo_table_closed_form :
    ∀ n : Fin 11, oneTwoTable n = oneTwoCoeff n.val := by
  native_decide

theorem oneTwo_table_values :
    (List.ofFn oneTwoTable) = [1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047] := by
  native_decide

def twoThreeCoeff (n : ℕ) : ℕ :=
  3 ^ (n + 1) - 2 ^ (n + 1)

def twoThreeTable : Fin 9 → ℕ :=
  ![1, 5, 19, 65, 211, 665, 2059, 6305, 19171]

theorem twoThree_table_closed_form :
    ∀ n : Fin 9, twoThreeTable n = twoThreeCoeff n.val := by
  native_decide

theorem twoThree_table_values :
    (List.ofFn twoThreeTable) = [1, 5, 19, 65, 211, 665, 2059, 6305, 19171] := by
  native_decide

def doublePoleCoeff (n : ℕ) : ℕ :=
  n + 1

def doublePoleTable : Fin 11 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

theorem doublePole_table_closed_form :
    ∀ n : Fin 11, doublePoleTable n = doublePoleCoeff n.val := by
  native_decide

theorem doublePole_table_values :
    (List.ofFn doublePoleTable) = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by
  native_decide

def triplePoleCoeff (n : ℕ) : ℕ :=
  ((n + 1) * (n + 2)) / 2

def triplePoleTable : Fin 9 → ℕ :=
  ![1, 3, 6, 10, 15, 21, 28, 36, 45]

theorem triplePole_table_closed_form :
    ∀ n : Fin 9, triplePoleTable n = triplePoleCoeff n.val := by
  native_decide

theorem triplePole_table_values :
    (List.ofFn triplePoleTable) = [1, 3, 6, 10, 15, 21, 28, 36, 45] := by
  native_decide

theorem triplePole_twice_table :
    ∀ n : Fin 9, 2 * triplePoleTable n = (n.val + 1) * (n.val + 2) := by
  native_decide

def shiftedOneTwoCoeff (n : ℕ) : ℕ :=
  2 ^ n - 1

def shiftedOneTwoTable : Fin 10 → ℕ :=
  ![0, 1, 3, 7, 15, 31, 63, 127, 255, 511]

theorem shiftedOneTwo_table_closed_form :
    ∀ n : Fin 10, shiftedOneTwoTable n = shiftedOneTwoCoeff n.val := by
  native_decide

theorem shiftedOneTwo_table_values :
    (List.ofFn shiftedOneTwoTable) = [0, 1, 3, 7, 15, 31, 63, 127, 255, 511] := by
  native_decide

theorem shiftedOneTwo_positive_index :
    ∀ n : Fin 10, 1 ≤ n.val → shiftedOneTwoTable n + 1 = 2 ^ n.val := by
  native_decide

def fibCoeff : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibCoeff (n + 1) + fibCoeff n

def fibTable : Fin 16 → ℕ :=
  ![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610]

theorem fib_table_closed_form :
    ∀ n : Fin 16, fibTable n = fibCoeff n.val := by
  native_decide

theorem fib_table_values :
    (List.ofFn fibTable) = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610] := by
  native_decide

theorem fib_table_recurrence :
    ∀ n : Fin 14,
      fibTable ⟨n.val + 2, by omega⟩ =
        fibTable ⟨n.val + 1, by omega⟩ + fibTable ⟨n.val, by omega⟩ := by
  native_decide



structure PartialFractionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PartialFractionsBudgetCertificate.controlled
    (c : PartialFractionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PartialFractionsBudgetCertificate.budgetControlled
    (c : PartialFractionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PartialFractionsBudgetCertificate.Ready
    (c : PartialFractionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PartialFractionsBudgetCertificate.size
    (c : PartialFractionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem partialFractions_budgetCertificate_le_size
    (c : PartialFractionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePartialFractionsBudgetCertificate :
    PartialFractionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePartialFractionsBudgetCertificate.Ready := by
  constructor
  · norm_num [PartialFractionsBudgetCertificate.controlled,
      samplePartialFractionsBudgetCertificate]
  · norm_num [PartialFractionsBudgetCertificate.budgetControlled,
      samplePartialFractionsBudgetCertificate]

example :
    samplePartialFractionsBudgetCertificate.certificateBudgetWindow ≤
      samplePartialFractionsBudgetCertificate.size := by
  apply partialFractions_budgetCertificate_le_size
  constructor
  · norm_num [PartialFractionsBudgetCertificate.controlled,
      samplePartialFractionsBudgetCertificate]
  · norm_num [PartialFractionsBudgetCertificate.budgetControlled,
      samplePartialFractionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePartialFractionsBudgetCertificate.Ready := by
  constructor
  · norm_num [PartialFractionsBudgetCertificate.controlled,
      samplePartialFractionsBudgetCertificate]
  · norm_num [PartialFractionsBudgetCertificate.budgetControlled,
      samplePartialFractionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePartialFractionsBudgetCertificate.certificateBudgetWindow ≤
      samplePartialFractionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PartialFractionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePartialFractionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePartialFractionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.PartialFractions
