import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Boundary-value bookkeeping models.

The finite data records boundary values, interior bounds, and admissible
defects for analytic boundary value problems.
-/

namespace AnalyticCombinatorics.AppB.BoundaryValueModels

structure BoundaryValueDatum where
  boundaryBudget : ℕ
  interiorBudget : ℕ
  defectBudget : ℕ
deriving DecidableEq, Repr

def boundaryControlsInterior (d : BoundaryValueDatum) : Prop :=
  d.interiorBudget ≤ d.boundaryBudget

def defectAbsorbed (d : BoundaryValueDatum) : Prop :=
  d.defectBudget ≤ d.boundaryBudget + d.interiorBudget

def boundaryValueReady (d : BoundaryValueDatum) : Prop :=
  boundaryControlsInterior d ∧ defectAbsorbed d

def boundaryValueBudget (d : BoundaryValueDatum) : ℕ :=
  d.boundaryBudget + d.interiorBudget + d.defectBudget

theorem boundaryValueReady.control {d : BoundaryValueDatum}
    (h : boundaryValueReady d) :
    boundaryControlsInterior d ∧ defectAbsorbed d ∧
      d.boundaryBudget ≤ boundaryValueBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold boundaryValueBudget
  omega

theorem boundaryBudget_le_total (d : BoundaryValueDatum) :
    d.boundaryBudget ≤ boundaryValueBudget d := by
  unfold boundaryValueBudget
  omega

def sampleBoundaryValue : BoundaryValueDatum :=
  { boundaryBudget := 9, interiorBudget := 5, defectBudget := 3 }

example : boundaryValueReady sampleBoundaryValue := by
  norm_num [boundaryValueReady, boundaryControlsInterior, defectAbsorbed, sampleBoundaryValue]

example : boundaryValueBudget sampleBoundaryValue = 17 := by
  native_decide

structure BoundaryValueWindow where
  boundaryWindow : ℕ
  interiorWindow : ℕ
  defectWindow : ℕ
  solutionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundaryValueWindow.interiorControlled (w : BoundaryValueWindow) : Prop :=
  w.interiorWindow ≤ w.boundaryWindow + w.slack

def BoundaryValueWindow.defectControlled (w : BoundaryValueWindow) : Prop :=
  w.defectWindow ≤ w.boundaryWindow + w.interiorWindow + w.slack

def boundaryValueWindowReady (w : BoundaryValueWindow) : Prop :=
  w.interiorControlled ∧ w.defectControlled ∧
    w.solutionBudget ≤ w.boundaryWindow + w.interiorWindow + w.defectWindow + w.slack

def BoundaryValueWindow.certificate (w : BoundaryValueWindow) : ℕ :=
  w.boundaryWindow + w.interiorWindow + w.defectWindow + w.solutionBudget + w.slack

theorem boundaryValue_solutionBudget_le_certificate (w : BoundaryValueWindow) :
    w.solutionBudget ≤ w.certificate := by
  unfold BoundaryValueWindow.certificate
  omega

def sampleBoundaryValueWindow : BoundaryValueWindow :=
  { boundaryWindow := 8, interiorWindow := 5, defectWindow := 3, solutionBudget := 17, slack := 1 }

example : boundaryValueWindowReady sampleBoundaryValueWindow := by
  norm_num [boundaryValueWindowReady, BoundaryValueWindow.interiorControlled,
    BoundaryValueWindow.defectControlled, sampleBoundaryValueWindow]


structure BoundaryValueModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundaryValueModelsBudgetCertificate.controlled
    (c : BoundaryValueModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BoundaryValueModelsBudgetCertificate.budgetControlled
    (c : BoundaryValueModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BoundaryValueModelsBudgetCertificate.Ready
    (c : BoundaryValueModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BoundaryValueModelsBudgetCertificate.size
    (c : BoundaryValueModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem boundaryValueModels_budgetCertificate_le_size
    (c : BoundaryValueModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBoundaryValueModelsBudgetCertificate :
    BoundaryValueModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBoundaryValueModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundaryValueModelsBudgetCertificate.controlled,
      sampleBoundaryValueModelsBudgetCertificate]
  · norm_num [BoundaryValueModelsBudgetCertificate.budgetControlled,
      sampleBoundaryValueModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBoundaryValueModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundaryValueModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBoundaryValueModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundaryValueModelsBudgetCertificate.controlled,
      sampleBoundaryValueModelsBudgetCertificate]
  · norm_num [BoundaryValueModelsBudgetCertificate.budgetControlled,
      sampleBoundaryValueModelsBudgetCertificate]

example :
    sampleBoundaryValueModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundaryValueModelsBudgetCertificate.size := by
  apply boundaryValueModels_budgetCertificate_le_size
  constructor
  · norm_num [BoundaryValueModelsBudgetCertificate.controlled,
      sampleBoundaryValueModelsBudgetCertificate]
  · norm_num [BoundaryValueModelsBudgetCertificate.budgetControlled,
      sampleBoundaryValueModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List BoundaryValueModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBoundaryValueModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBoundaryValueModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.BoundaryValueModels
