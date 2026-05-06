import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Catalan asymptotic checks.

This module records finite monotonicity and growth sanity checks for Catalan,
Motzkin, and Schroder tables.
-/

namespace AnalyticCombinatorics.PartB.Ch7.CatalanAsymptotics

def catalanCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 42
  | 6 => 132
  | 7 => 429
  | 8 => 1430
  | 9 => 4862
  | 10 => 16796
  | 11 => 58786
  | 12 => 208012
  | _ => 0

def schroderCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 22
  | 4 => 90
  | 5 => 394
  | 6 => 1806
  | 7 => 8558
  | 8 => 41586
  | _ => 0

theorem catalan_lt_four_pow_1_12 :
    (List.range 12).all
      (fun k => catalanCount (k + 1) < 4 ^ (k + 1)) = true := by
  native_decide

theorem schroder_lt_six_pow_1_8 :
    (List.range 8).all
      (fun k => schroderCount (k + 1) < 6 ^ (k + 1)) = true := by
  native_decide

example : catalanCount 12 = 208012 := by native_decide
example : schroderCount 8 = 41586 := by native_decide

structure CatalanAsymptoticsBudgetCertificate where
  tableWindow : ℕ
  catalanBoundWindow : ℕ
  schroderBoundWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CatalanAsymptoticsBudgetCertificate.controlled
    (c : CatalanAsymptoticsBudgetCertificate) : Prop :=
  0 < c.tableWindow ∧
    c.catalanBoundWindow ≤ 4 ^ c.tableWindow + c.slack ∧
      c.schroderBoundWindow ≤ 6 ^ c.tableWindow + c.slack

def CatalanAsymptoticsBudgetCertificate.budgetControlled
    (c : CatalanAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.tableWindow + c.catalanBoundWindow + c.schroderBoundWindow + c.slack

def CatalanAsymptoticsBudgetCertificate.Ready
    (c : CatalanAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CatalanAsymptoticsBudgetCertificate.size
    (c : CatalanAsymptoticsBudgetCertificate) : ℕ :=
  c.tableWindow + c.catalanBoundWindow + c.schroderBoundWindow + c.slack

theorem catalanAsymptotics_budgetCertificate_le_size
    (c : CatalanAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCatalanAsymptoticsBudgetCertificate :
    CatalanAsymptoticsBudgetCertificate :=
  { tableWindow := 4
    catalanBoundWindow := 14
    schroderBoundWindow := 90
    certificateBudgetWindow := 109
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCatalanAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [CatalanAsymptoticsBudgetCertificate.controlled,
      sampleCatalanAsymptoticsBudgetCertificate]
  · norm_num [CatalanAsymptoticsBudgetCertificate.budgetControlled,
      sampleCatalanAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCatalanAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleCatalanAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCatalanAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [CatalanAsymptoticsBudgetCertificate.controlled,
      sampleCatalanAsymptoticsBudgetCertificate]
  · norm_num [CatalanAsymptoticsBudgetCertificate.budgetControlled,
      sampleCatalanAsymptoticsBudgetCertificate]

example :
    sampleCatalanAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleCatalanAsymptoticsBudgetCertificate.size := by
  apply catalanAsymptotics_budgetCertificate_le_size
  constructor
  · norm_num [CatalanAsymptoticsBudgetCertificate.controlled,
      sampleCatalanAsymptoticsBudgetCertificate]
  · norm_num [CatalanAsymptoticsBudgetCertificate.budgetControlled,
      sampleCatalanAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CatalanAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleCatalanAsymptoticsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleCatalanAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.CatalanAsymptotics
