import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Pointed product schemas.

The file records finite coefficient contributions when a product
construction is pointed.
-/

namespace AnalyticCombinatorics.PartA.Ch1.PointedProductSchemas

def productCoeff (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).map (fun k => a k * b (n - k)) |>.sum

def pointedProductCoeff (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  n * productCoeff a b n

theorem productCoeff_zero (a b : ℕ → ℕ) :
    productCoeff a b 0 = a 0 * b 0 := by
  simp [productCoeff]

theorem pointedProductCoeff_zero (a b : ℕ → ℕ) :
    pointedProductCoeff a b 0 = 0 := by
  simp [pointedProductCoeff]

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

example : pointedProductCoeff sampleLeft sampleRight 1 = 10 := by
  native_decide

structure PointedProductWindow where
  size : ℕ
  productMass : ℕ
  pointedMass : ℕ
  pointingSlack : ℕ
deriving DecidableEq, Repr

def PointedProductWindow.pointingBudget (w : PointedProductWindow) : ℕ :=
  w.size * w.productMass + w.pointingSlack

def PointedProductWindow.ready (w : PointedProductWindow) : Prop :=
  w.pointedMass ≤ w.pointingBudget

def PointedProductWindow.nonzeroPointing (w : PointedProductWindow) : Prop :=
  0 < w.size

def PointedProductWindow.certificate (w : PointedProductWindow) : ℕ :=
  w.size + w.productMass + w.pointedMass + w.pointingSlack

theorem pointedMass_le_certificate (w : PointedProductWindow) :
    w.pointedMass ≤ w.certificate := by
  unfold PointedProductWindow.certificate
  omega

def samplePointedProductWindow : PointedProductWindow :=
  { size := 1, productMass := 10, pointedMass := 10, pointingSlack := 0 }

example : samplePointedProductWindow.ready := by
  norm_num [samplePointedProductWindow, PointedProductWindow.ready,
    PointedProductWindow.pointingBudget]

example : samplePointedProductWindow.nonzeroPointing := by
  norm_num [samplePointedProductWindow, PointedProductWindow.nonzeroPointing]


structure PointedProductSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PointedProductSchemasBudgetCertificate.controlled
    (c : PointedProductSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PointedProductSchemasBudgetCertificate.budgetControlled
    (c : PointedProductSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PointedProductSchemasBudgetCertificate.Ready
    (c : PointedProductSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PointedProductSchemasBudgetCertificate.size
    (c : PointedProductSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem pointedProductSchemas_budgetCertificate_le_size
    (c : PointedProductSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePointedProductSchemasBudgetCertificate :
    PointedProductSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePointedProductSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PointedProductSchemasBudgetCertificate.controlled,
      samplePointedProductSchemasBudgetCertificate]
  · norm_num [PointedProductSchemasBudgetCertificate.budgetControlled,
      samplePointedProductSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePointedProductSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePointedProductSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePointedProductSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PointedProductSchemasBudgetCertificate.controlled,
      samplePointedProductSchemasBudgetCertificate]
  · norm_num [PointedProductSchemasBudgetCertificate.budgetControlled,
      samplePointedProductSchemasBudgetCertificate]

example :
    samplePointedProductSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePointedProductSchemasBudgetCertificate.size := by
  apply pointedProductSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PointedProductSchemasBudgetCertificate.controlled,
      samplePointedProductSchemasBudgetCertificate]
  · norm_num [PointedProductSchemasBudgetCertificate.budgetControlled,
      samplePointedProductSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PointedProductSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePointedProductSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePointedProductSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.PointedProductSchemas
