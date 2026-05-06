import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Algebraic singularity coefficient checks.

This module records finite Catalan and Motzkin checks associated with
square-root singularities.
-/

namespace AnalyticCombinatorics.PartB.Ch6.AlgebraicSingularity

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
  | _ => 0

def motzkinCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 9
  | 5 => 21
  | 6 => 51
  | 7 => 127
  | 8 => 323
  | 9 => 835
  | 10 => 2188
  | _ => 0

theorem catalan_upper_4n_1_10 :
    (List.range 10).all
      (fun k => catalanCount (k + 1) < 4 ^ (k + 1)) = true := by
  native_decide

theorem motzkin_upper_3n_1_10 :
    (List.range 10).all
      (fun k => motzkinCount (k + 1) < 3 ^ (k + 1)) = true := by
  native_decide

example : catalanCount 10 = 16796 := by native_decide
example : motzkinCount 10 = 2188 := by native_decide

structure AlgebraicSingularityBudgetCertificate where
  tableWindow : ℕ
  catalanBoundWindow : ℕ
  motzkinBoundWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlgebraicSingularityBudgetCertificate.controlled
    (c : AlgebraicSingularityBudgetCertificate) : Prop :=
  0 < c.tableWindow ∧
    c.catalanBoundWindow ≤ 4 ^ c.tableWindow + c.slack ∧
      c.motzkinBoundWindow ≤ 3 ^ c.tableWindow + c.slack

def AlgebraicSingularityBudgetCertificate.budgetControlled
    (c : AlgebraicSingularityBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.tableWindow + c.catalanBoundWindow + c.motzkinBoundWindow + c.slack

def AlgebraicSingularityBudgetCertificate.Ready
    (c : AlgebraicSingularityBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlgebraicSingularityBudgetCertificate.size
    (c : AlgebraicSingularityBudgetCertificate) : ℕ :=
  c.tableWindow + c.catalanBoundWindow + c.motzkinBoundWindow + c.slack

theorem algebraicSingularity_budgetCertificate_le_size
    (c : AlgebraicSingularityBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAlgebraicSingularityBudgetCertificate :
    AlgebraicSingularityBudgetCertificate :=
  { tableWindow := 4
    catalanBoundWindow := 14
    motzkinBoundWindow := 9
    certificateBudgetWindow := 28
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAlgebraicSingularityBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicSingularityBudgetCertificate.controlled,
      sampleAlgebraicSingularityBudgetCertificate]
  · norm_num [AlgebraicSingularityBudgetCertificate.budgetControlled,
      sampleAlgebraicSingularityBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlgebraicSingularityBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicSingularityBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAlgebraicSingularityBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicSingularityBudgetCertificate.controlled,
      sampleAlgebraicSingularityBudgetCertificate]
  · norm_num [AlgebraicSingularityBudgetCertificate.budgetControlled,
      sampleAlgebraicSingularityBudgetCertificate]

example :
    sampleAlgebraicSingularityBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicSingularityBudgetCertificate.size := by
  apply algebraicSingularity_budgetCertificate_le_size
  constructor
  · norm_num [AlgebraicSingularityBudgetCertificate.controlled,
      sampleAlgebraicSingularityBudgetCertificate]
  · norm_num [AlgebraicSingularityBudgetCertificate.budgetControlled,
      sampleAlgebraicSingularityBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AlgebraicSingularityBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAlgebraicSingularityBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAlgebraicSingularityBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.AlgebraicSingularity
