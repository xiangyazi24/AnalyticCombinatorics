import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Pointing schemas for labelled and unlabelled classes.

Pointing multiplies coefficient counts by the size index; this file records
the elementary coefficient bookkeeping.
-/

namespace AnalyticCombinatorics.PartA.Ch1.PointingSchemas

def pointedCoeff (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  n * a n

def rootedCoeff (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (n + 1) * a (n + 1)

def vanishesAtZero (a : ℕ → ℕ) : Prop :=
  a 0 = 0

theorem pointedCoeff_zero (a : ℕ → ℕ) :
    pointedCoeff a 0 = 0 := by
  simp [pointedCoeff]

theorem rootedCoeff_eq_pointed_shift (a : ℕ → ℕ) (n : ℕ) :
    rootedCoeff a n = pointedCoeff a (n + 1) := by
  rfl

theorem pointedCoeff_mono {a b : ℕ → ℕ}
    (h : ∀ n, a n ≤ b n) :
    ∀ n, pointedCoeff a n ≤ pointedCoeff b n := by
  intro n
  unfold pointedCoeff
  exact Nat.mul_le_mul_left n (h n)

def sampleClass : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | _ => 1

example : vanishesAtZero sampleClass := by
  norm_num [vanishesAtZero, sampleClass]

example : pointedCoeff sampleClass 2 = 6 := by
  native_decide

example : rootedCoeff sampleClass 1 = 6 := by
  native_decide

structure PointingWindow where
  baseSize : ℕ
  pointChoices : ℕ
  rootedChoices : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PointingWindow.pointChoicesControlled (w : PointingWindow) : Prop :=
  w.pointChoices ≤ w.baseSize + w.slack

def PointingWindow.rootedChoicesControlled (w : PointingWindow) : Prop :=
  w.rootedChoices ≤ w.baseSize + w.pointChoices + w.slack

def pointingWindowReady (w : PointingWindow) : Prop :=
  0 < w.baseSize ∧
    w.pointChoicesControlled ∧
    w.rootedChoicesControlled

def PointingWindow.certificate (w : PointingWindow) : ℕ :=
  w.baseSize + w.pointChoices + w.slack

theorem pointing_rootedChoices_le_certificate {w : PointingWindow}
    (h : pointingWindowReady w) :
    w.rootedChoices ≤ w.certificate := by
  rcases h with ⟨_, _, hrooted⟩
  exact hrooted

def samplePointingWindow : PointingWindow :=
  { baseSize := 6, pointChoices := 5, rootedChoices := 10, slack := 0 }

example : pointingWindowReady samplePointingWindow := by
  norm_num [pointingWindowReady, PointingWindow.pointChoicesControlled,
    PointingWindow.rootedChoicesControlled, samplePointingWindow]

example : samplePointingWindow.certificate = 11 := by
  native_decide


structure PointingSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PointingSchemasBudgetCertificate.controlled
    (c : PointingSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PointingSchemasBudgetCertificate.budgetControlled
    (c : PointingSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PointingSchemasBudgetCertificate.Ready
    (c : PointingSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PointingSchemasBudgetCertificate.size
    (c : PointingSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem pointingSchemas_budgetCertificate_le_size
    (c : PointingSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePointingSchemasBudgetCertificate :
    PointingSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePointingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PointingSchemasBudgetCertificate.controlled,
      samplePointingSchemasBudgetCertificate]
  · norm_num [PointingSchemasBudgetCertificate.budgetControlled,
      samplePointingSchemasBudgetCertificate]

example :
    samplePointingSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePointingSchemasBudgetCertificate.size := by
  apply pointingSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PointingSchemasBudgetCertificate.controlled,
      samplePointingSchemasBudgetCertificate]
  · norm_num [PointingSchemasBudgetCertificate.budgetControlled,
      samplePointingSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePointingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PointingSchemasBudgetCertificate.controlled,
      samplePointingSchemasBudgetCertificate]
  · norm_num [PointingSchemasBudgetCertificate.budgetControlled,
      samplePointingSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePointingSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePointingSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PointingSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePointingSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePointingSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.PointingSchemas
