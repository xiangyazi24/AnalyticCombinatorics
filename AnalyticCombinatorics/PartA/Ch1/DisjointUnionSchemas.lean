import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Disjoint union schemas.

The module records coefficientwise addition for sum constructions of
ordinary combinatorial classes.
-/

namespace AnalyticCombinatorics.PartA.Ch1.DisjointUnionSchemas

def sumCoeff (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  a n + b n

def sumPrefixMass (a b : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).map (sumCoeff a b) |>.sum

theorem sumCoeff_comm (a b : ℕ → ℕ) (n : ℕ) :
    sumCoeff a b n = sumCoeff b a n := by
  unfold sumCoeff
  omega

theorem sumPrefixMass_zero (a b : ℕ → ℕ) :
    sumPrefixMass a b 0 = a 0 + b 0 := by
  simp [sumPrefixMass, sumCoeff]

def sampleA : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | _ => 0

def sampleB : ℕ → ℕ
  | 0 => 3
  | 1 => 4
  | _ => 0

example : sumCoeff sampleA sampleB 1 = 6 := by
  native_decide

example : sumPrefixMass sampleA sampleB 1 = 10 := by
  native_decide

structure DisjointUnionWindow where
  size : ℕ
  leftMass : ℕ
  rightMass : ℕ
  unionMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DisjointUnionWindow.sumBudget (w : DisjointUnionWindow) : ℕ :=
  w.leftMass + w.rightMass + w.slack

def DisjointUnionWindow.ready (w : DisjointUnionWindow) : Prop :=
  w.unionMass ≤ w.sumBudget

def DisjointUnionWindow.certificate (w : DisjointUnionWindow) : ℕ :=
  w.size + w.leftMass + w.rightMass + w.unionMass + w.slack

theorem unionMass_le_certificate (w : DisjointUnionWindow) :
    w.unionMass ≤ w.certificate := by
  unfold DisjointUnionWindow.certificate
  omega

def sampleDisjointUnionWindow : DisjointUnionWindow :=
  { size := 1, leftMass := 2, rightMass := 4, unionMass := 6, slack := 0 }

example : sampleDisjointUnionWindow.ready := by
  norm_num [sampleDisjointUnionWindow, DisjointUnionWindow.ready,
    DisjointUnionWindow.sumBudget]


structure DisjointUnionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DisjointUnionSchemasBudgetCertificate.controlled
    (c : DisjointUnionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DisjointUnionSchemasBudgetCertificate.budgetControlled
    (c : DisjointUnionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DisjointUnionSchemasBudgetCertificate.Ready
    (c : DisjointUnionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DisjointUnionSchemasBudgetCertificate.size
    (c : DisjointUnionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem disjointUnionSchemas_budgetCertificate_le_size
    (c : DisjointUnionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDisjointUnionSchemasBudgetCertificate :
    DisjointUnionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDisjointUnionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DisjointUnionSchemasBudgetCertificate.controlled,
      sampleDisjointUnionSchemasBudgetCertificate]
  · norm_num [DisjointUnionSchemasBudgetCertificate.budgetControlled,
      sampleDisjointUnionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDisjointUnionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDisjointUnionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDisjointUnionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DisjointUnionSchemasBudgetCertificate.controlled,
      sampleDisjointUnionSchemasBudgetCertificate]
  · norm_num [DisjointUnionSchemasBudgetCertificate.budgetControlled,
      sampleDisjointUnionSchemasBudgetCertificate]

example :
    sampleDisjointUnionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDisjointUnionSchemasBudgetCertificate.size := by
  apply disjointUnionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DisjointUnionSchemasBudgetCertificate.controlled,
      sampleDisjointUnionSchemasBudgetCertificate]
  · norm_num [DisjointUnionSchemasBudgetCertificate.budgetControlled,
      sampleDisjointUnionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List DisjointUnionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDisjointUnionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDisjointUnionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.DisjointUnionSchemas
