import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Square-root singularity schema bookkeeping.

The finite record captures nonzero amplitude, analytic remainder, and a
positive local scale for transfer statements.
-/

namespace AnalyticCombinatorics.PartB.Ch6.SquareRootSingularitySchemas

structure SquareRootData where
  amplitude : ℕ
  localScale : ℕ
  remainderBudget : ℕ
deriving DecidableEq, Repr

def nonzeroAmplitude (d : SquareRootData) : Prop :=
  0 < d.amplitude

def positiveLocalScale (d : SquareRootData) : Prop :=
  0 < d.localScale

def squareRootReady (d : SquareRootData) : Prop :=
  nonzeroAmplitude d ∧ positiveLocalScale d

def singularBudget (d : SquareRootData) : ℕ :=
  d.amplitude * d.localScale + d.remainderBudget

theorem squareRootReady.scale {d : SquareRootData}
    (h : squareRootReady d) :
    positiveLocalScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem singularBudget_ge_remainder (d : SquareRootData) :
    d.remainderBudget ≤ singularBudget d := by
  unfold singularBudget
  omega

def sampleSquareRoot : SquareRootData :=
  { amplitude := 3, localScale := 4, remainderBudget := 2 }

example : squareRootReady sampleSquareRoot := by
  norm_num [squareRootReady, nonzeroAmplitude, positiveLocalScale, sampleSquareRoot]

example : singularBudget sampleSquareRoot = 14 := by
  native_decide

structure SquareRootWindow where
  amplitude : ℕ
  localScale : ℕ
  remainderBudget : ℕ
  coefficientMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SquareRootWindow.coefficientControlled (w : SquareRootWindow) : Prop :=
  w.coefficientMass ≤ w.amplitude * w.localScale + w.remainderBudget + w.slack

def squareRootWindowReady (w : SquareRootWindow) : Prop :=
  0 < w.amplitude ∧
    0 < w.localScale ∧
    w.coefficientControlled

def SquareRootWindow.certificate (w : SquareRootWindow) : ℕ :=
  w.amplitude * w.localScale + w.remainderBudget + w.slack

theorem squareRoot_coefficientMass_le_certificate {w : SquareRootWindow}
    (h : squareRootWindowReady w) :
    w.coefficientMass ≤ w.certificate := by
  rcases h with ⟨_, _, hcoeff⟩
  exact hcoeff

def sampleSquareRootWindow : SquareRootWindow :=
  { amplitude := 3, localScale := 4, remainderBudget := 2, coefficientMass := 12, slack := 0 }

example : squareRootWindowReady sampleSquareRootWindow := by
  norm_num [squareRootWindowReady, SquareRootWindow.coefficientControlled,
    sampleSquareRootWindow]

example : sampleSquareRootWindow.certificate = 14 := by
  native_decide


structure SquareRootSingularitySchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SquareRootSingularitySchemasBudgetCertificate.controlled
    (c : SquareRootSingularitySchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SquareRootSingularitySchemasBudgetCertificate.budgetControlled
    (c : SquareRootSingularitySchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SquareRootSingularitySchemasBudgetCertificate.Ready
    (c : SquareRootSingularitySchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SquareRootSingularitySchemasBudgetCertificate.size
    (c : SquareRootSingularitySchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem squareRootSingularitySchemas_budgetCertificate_le_size
    (c : SquareRootSingularitySchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSquareRootSingularitySchemasBudgetCertificate :
    SquareRootSingularitySchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSquareRootSingularitySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SquareRootSingularitySchemasBudgetCertificate.controlled,
      sampleSquareRootSingularitySchemasBudgetCertificate]
  · norm_num [SquareRootSingularitySchemasBudgetCertificate.budgetControlled,
      sampleSquareRootSingularitySchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSquareRootSingularitySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSquareRootSingularitySchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSquareRootSingularitySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SquareRootSingularitySchemasBudgetCertificate.controlled,
      sampleSquareRootSingularitySchemasBudgetCertificate]
  · norm_num [SquareRootSingularitySchemasBudgetCertificate.budgetControlled,
      sampleSquareRootSingularitySchemasBudgetCertificate]

example :
    sampleSquareRootSingularitySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSquareRootSingularitySchemasBudgetCertificate.size := by
  apply squareRootSingularitySchemas_budgetCertificate_le_size
  constructor
  · norm_num [SquareRootSingularitySchemasBudgetCertificate.controlled,
      sampleSquareRootSingularitySchemasBudgetCertificate]
  · norm_num [SquareRootSingularitySchemasBudgetCertificate.budgetControlled,
      sampleSquareRootSingularitySchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SquareRootSingularitySchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSquareRootSingularitySchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSquareRootSingularitySchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.SquareRootSingularitySchemas
