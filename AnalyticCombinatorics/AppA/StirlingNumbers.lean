import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix A: Stirling numbers.

Finite triangular-table windows for Stirling numbers of both kinds.
-/

namespace AnalyticCombinatorics.AppA.StirlingNumbers

/-- Recurrence residual for Stirling numbers of the second kind. -/
def stirlingSecondRecurrenceResidual (S : ℕ → ℕ → ℕ) (n k : ℕ) : ℤ :=
  (S (n + 1) k : ℤ) - (k * S n k + S n (k - 1) : ℕ)

def stirlingSecondSmall : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 1 => 1
  | 3, 2 => 3
  | 3, 3 => 1
  | 4, 1 => 1
  | 4, 2 => 7
  | 4, 3 => 6
  | 4, 4 => 1
  | _, _ => 0

theorem stirlingSecondSmall_samples :
    stirlingSecondSmall 4 2 = 7 ∧
    stirlingSecondSmall 4 3 = 6 ∧
    stirlingSecondSmall 3 2 = 3 := by
  native_decide

/-- Finite recurrence audit over the initial small Stirling table. -/
def stirlingSecondRecurrenceCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    (List.range (N + 1)).all fun k =>
      if n = 0 ∨ k = 0 ∨ n + 1 > 4 then true
      else stirlingSecondRecurrenceResidual stirlingSecondSmall n k = 0

theorem stirlingSecondSmall_recurrenceWindow :
    stirlingSecondRecurrenceCheck 3 = true := by
  unfold stirlingSecondRecurrenceCheck stirlingSecondRecurrenceResidual
    stirlingSecondSmall
  native_decide

structure StirlingTableWindow where
  rowWindow : ℕ
  columnWindow : ℕ
  entryWindow : ℕ
  tableSlack : ℕ
deriving DecidableEq, Repr

def stirlingTableReady (w : StirlingTableWindow) : Prop :=
  0 < w.rowWindow ∧
    w.columnWindow ≤ w.rowWindow ∧
      w.entryWindow ≤ 2 ^ w.rowWindow + w.tableSlack

def stirlingTableBudget (w : StirlingTableWindow) : ℕ :=
  w.rowWindow + w.columnWindow + w.entryWindow + w.tableSlack

theorem columnWindow_le_budget (w : StirlingTableWindow) :
    w.columnWindow ≤ stirlingTableBudget w := by
  unfold stirlingTableBudget
  omega

def sampleStirlingTableWindow : StirlingTableWindow :=
  { rowWindow := 4, columnWindow := 2, entryWindow := 7, tableSlack := 0 }

example : stirlingTableReady sampleStirlingTableWindow := by
  norm_num [stirlingTableReady, sampleStirlingTableWindow]

structure StirlingNumbersBudgetCertificate where
  rowWindow : ℕ
  columnWindow : ℕ
  entryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StirlingNumbersBudgetCertificate.controlled
    (c : StirlingNumbersBudgetCertificate) : Prop :=
  0 < c.rowWindow ∧ c.columnWindow ≤ c.rowWindow ∧
    c.entryWindow ≤ 2 ^ c.rowWindow + c.slack

def StirlingNumbersBudgetCertificate.budgetControlled
    (c : StirlingNumbersBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.rowWindow + c.columnWindow + c.entryWindow + c.slack

def StirlingNumbersBudgetCertificate.Ready
    (c : StirlingNumbersBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StirlingNumbersBudgetCertificate.size
    (c : StirlingNumbersBudgetCertificate) : ℕ :=
  c.rowWindow + c.columnWindow + c.entryWindow + c.slack

theorem stirlingNumbers_budgetCertificate_le_size
    (c : StirlingNumbersBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleStirlingNumbersBudgetCertificate :
    StirlingNumbersBudgetCertificate :=
  { rowWindow := 4
    columnWindow := 2
    entryWindow := 7
    certificateBudgetWindow := 14
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleStirlingNumbersBudgetCertificate.Ready := by
  constructor
  · norm_num [StirlingNumbersBudgetCertificate.controlled,
      sampleStirlingNumbersBudgetCertificate]
  · norm_num [StirlingNumbersBudgetCertificate.budgetControlled,
      sampleStirlingNumbersBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleStirlingNumbersBudgetCertificate.certificateBudgetWindow ≤
      sampleStirlingNumbersBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleStirlingNumbersBudgetCertificate.Ready := by
  constructor
  · norm_num [StirlingNumbersBudgetCertificate.controlled,
      sampleStirlingNumbersBudgetCertificate]
  · norm_num [StirlingNumbersBudgetCertificate.budgetControlled,
      sampleStirlingNumbersBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List StirlingNumbersBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleStirlingNumbersBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleStirlingNumbersBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.StirlingNumbers
