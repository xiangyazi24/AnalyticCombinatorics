import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cartesian product schemas for ordinary classes.

The file provides finite coefficient convolutions for product
constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.CartesianProductSchemas

def productCoeff (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).map (fun k => a k * b (n - k)) |>.sum

def productPrefixMass (a b : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).map (productCoeff a b) |>.sum

theorem productCoeff_zero (a b : ℕ → ℕ) :
    productCoeff a b 0 = a 0 * b 0 := by
  simp [productCoeff]

theorem productPrefixMass_zero (a b : ℕ → ℕ) :
    productPrefixMass a b 0 = a 0 * b 0 := by
  simp [productPrefixMass, productCoeff]

def sampleLeft : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | _ => 0

def sampleRight : ℕ → ℕ
  | 0 => 3
  | 1 => 4
  | _ => 0

example : productCoeff sampleLeft sampleRight 1 = 10 := by
  native_decide

example : productPrefixMass sampleLeft sampleRight 1 = 13 := by
  native_decide

structure CartesianProductWindow where
  size : ℕ
  leftPrefixMass : ℕ
  rightPrefixMass : ℕ
  productMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CartesianProductWindow.massBudget (w : CartesianProductWindow) : ℕ :=
  w.leftPrefixMass * w.rightPrefixMass + w.slack

def CartesianProductWindow.ready (w : CartesianProductWindow) : Prop :=
  w.productMass ≤ w.massBudget

def CartesianProductWindow.certificate (w : CartesianProductWindow) : ℕ :=
  w.size + w.leftPrefixMass + w.rightPrefixMass + w.productMass + w.slack

theorem productMass_le_certificate (w : CartesianProductWindow) :
    w.productMass ≤ w.certificate := by
  unfold CartesianProductWindow.certificate
  omega

def sampleCartesianProductWindow : CartesianProductWindow :=
  { size := 1, leftPrefixMass := 3, rightPrefixMass := 7, productMass := 13, slack := 0 }

example : sampleCartesianProductWindow.ready := by
  norm_num [sampleCartesianProductWindow, CartesianProductWindow.ready,
    CartesianProductWindow.massBudget]


structure CartesianProductSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CartesianProductSchemasBudgetCertificate.controlled
    (c : CartesianProductSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CartesianProductSchemasBudgetCertificate.budgetControlled
    (c : CartesianProductSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CartesianProductSchemasBudgetCertificate.Ready
    (c : CartesianProductSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CartesianProductSchemasBudgetCertificate.size
    (c : CartesianProductSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cartesianProductSchemas_budgetCertificate_le_size
    (c : CartesianProductSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCartesianProductSchemasBudgetCertificate :
    CartesianProductSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCartesianProductSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CartesianProductSchemasBudgetCertificate.controlled,
      sampleCartesianProductSchemasBudgetCertificate]
  · norm_num [CartesianProductSchemasBudgetCertificate.budgetControlled,
      sampleCartesianProductSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCartesianProductSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCartesianProductSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCartesianProductSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CartesianProductSchemasBudgetCertificate.controlled,
      sampleCartesianProductSchemasBudgetCertificate]
  · norm_num [CartesianProductSchemasBudgetCertificate.budgetControlled,
      sampleCartesianProductSchemasBudgetCertificate]

example :
    sampleCartesianProductSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCartesianProductSchemasBudgetCertificate.size := by
  apply cartesianProductSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CartesianProductSchemasBudgetCertificate.controlled,
      sampleCartesianProductSchemasBudgetCertificate]
  · norm_num [CartesianProductSchemasBudgetCertificate.budgetControlled,
      sampleCartesianProductSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CartesianProductSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCartesianProductSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCartesianProductSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.CartesianProductSchemas
