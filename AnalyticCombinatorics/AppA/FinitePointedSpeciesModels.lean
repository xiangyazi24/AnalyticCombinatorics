import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite pointed species models.

The finite schema records labelled atoms, point choices, and orbit slack
for pointed species data.
-/

namespace AnalyticCombinatorics.AppA.FinitePointedSpeciesModels

structure PointedSpeciesData where
  labelledAtoms : ℕ
  pointChoices : ℕ
  orbitSlack : ℕ
deriving DecidableEq, Repr

def labelledAtomsPositive (d : PointedSpeciesData) : Prop :=
  0 < d.labelledAtoms

def pointChoicesControlled (d : PointedSpeciesData) : Prop :=
  d.pointChoices ≤ d.labelledAtoms + d.orbitSlack

def pointedSpeciesReady (d : PointedSpeciesData) : Prop :=
  labelledAtomsPositive d ∧ pointChoicesControlled d

def pointedSpeciesBudget (d : PointedSpeciesData) : ℕ :=
  d.labelledAtoms + d.pointChoices + d.orbitSlack

theorem pointedSpeciesReady.atoms {d : PointedSpeciesData}
    (h : pointedSpeciesReady d) :
    labelledAtomsPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem pointChoices_le_pointedSpeciesBudget (d : PointedSpeciesData) :
    d.pointChoices ≤ pointedSpeciesBudget d := by
  unfold pointedSpeciesBudget
  omega

def samplePointedSpeciesData : PointedSpeciesData :=
  { labelledAtoms := 6, pointChoices := 8, orbitSlack := 3 }

example : pointedSpeciesReady samplePointedSpeciesData := by
  norm_num [pointedSpeciesReady, labelledAtomsPositive]
  norm_num [pointChoicesControlled, samplePointedSpeciesData]

example : pointedSpeciesBudget samplePointedSpeciesData = 17 := by
  native_decide

structure PointedSpeciesWindow where
  labelledAtoms : ℕ
  pointChoices : ℕ
  orbitSlack : ℕ
  pointedOrbitBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PointedSpeciesWindow.pointChoicesControlled (w : PointedSpeciesWindow) : Prop :=
  w.pointChoices ≤ w.labelledAtoms + w.orbitSlack + w.slack

def PointedSpeciesWindow.orbitControlled (w : PointedSpeciesWindow) : Prop :=
  w.pointedOrbitBudget ≤ w.labelledAtoms + w.pointChoices + w.orbitSlack + w.slack

def pointedSpeciesWindowReady (w : PointedSpeciesWindow) : Prop :=
  0 < w.labelledAtoms ∧
    w.pointChoicesControlled ∧
    w.orbitControlled

def PointedSpeciesWindow.certificate (w : PointedSpeciesWindow) : ℕ :=
  w.labelledAtoms + w.pointChoices + w.orbitSlack + w.slack

theorem pointedSpecies_orbitBudget_le_certificate {w : PointedSpeciesWindow}
    (h : pointedSpeciesWindowReady w) :
    w.pointedOrbitBudget ≤ w.certificate := by
  rcases h with ⟨_, _, horbit⟩
  exact horbit

def samplePointedSpeciesWindow : PointedSpeciesWindow :=
  { labelledAtoms := 6, pointChoices := 8, orbitSlack := 3, pointedOrbitBudget := 15, slack := 0 }

example : pointedSpeciesWindowReady samplePointedSpeciesWindow := by
  norm_num [pointedSpeciesWindowReady, PointedSpeciesWindow.pointChoicesControlled,
    PointedSpeciesWindow.orbitControlled, samplePointedSpeciesWindow]

example : samplePointedSpeciesWindow.certificate = 17 := by
  native_decide


structure FinitePointedSpeciesModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FinitePointedSpeciesModelsBudgetCertificate.controlled
    (c : FinitePointedSpeciesModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FinitePointedSpeciesModelsBudgetCertificate.budgetControlled
    (c : FinitePointedSpeciesModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FinitePointedSpeciesModelsBudgetCertificate.Ready
    (c : FinitePointedSpeciesModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FinitePointedSpeciesModelsBudgetCertificate.size
    (c : FinitePointedSpeciesModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finitePointedSpeciesModels_budgetCertificate_le_size
    (c : FinitePointedSpeciesModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFinitePointedSpeciesModelsBudgetCertificate :
    FinitePointedSpeciesModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFinitePointedSpeciesModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePointedSpeciesModelsBudgetCertificate.controlled,
      sampleFinitePointedSpeciesModelsBudgetCertificate]
  · norm_num [FinitePointedSpeciesModelsBudgetCertificate.budgetControlled,
      sampleFinitePointedSpeciesModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFinitePointedSpeciesModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePointedSpeciesModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFinitePointedSpeciesModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePointedSpeciesModelsBudgetCertificate.controlled,
      sampleFinitePointedSpeciesModelsBudgetCertificate]
  · norm_num [FinitePointedSpeciesModelsBudgetCertificate.budgetControlled,
      sampleFinitePointedSpeciesModelsBudgetCertificate]

example :
    sampleFinitePointedSpeciesModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePointedSpeciesModelsBudgetCertificate.size := by
  apply finitePointedSpeciesModels_budgetCertificate_le_size
  constructor
  · norm_num [FinitePointedSpeciesModelsBudgetCertificate.controlled,
      sampleFinitePointedSpeciesModelsBudgetCertificate]
  · norm_num [FinitePointedSpeciesModelsBudgetCertificate.budgetControlled,
      sampleFinitePointedSpeciesModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FinitePointedSpeciesModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFinitePointedSpeciesModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFinitePointedSpeciesModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FinitePointedSpeciesModels
