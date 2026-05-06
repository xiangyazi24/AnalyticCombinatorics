import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random occupation measure schemas.

The finite record stores state cells, occupation budget, and time slack.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomOccupationMeasureSchemas

structure RandomOccupationMeasureData where
  stateCells : ℕ
  occupationBudget : ℕ
  timeSlack : ℕ
deriving DecidableEq, Repr

def stateCellsPositive (d : RandomOccupationMeasureData) : Prop :=
  0 < d.stateCells

def occupationBudgetControlled (d : RandomOccupationMeasureData) : Prop :=
  d.occupationBudget ≤ d.stateCells + d.timeSlack

def randomOccupationMeasureReady (d : RandomOccupationMeasureData) : Prop :=
  stateCellsPositive d ∧ occupationBudgetControlled d

def randomOccupationMeasureBudget (d : RandomOccupationMeasureData) : ℕ :=
  d.stateCells + d.occupationBudget + d.timeSlack

theorem randomOccupationMeasureReady.states
    {d : RandomOccupationMeasureData}
    (h : randomOccupationMeasureReady d) :
    stateCellsPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem occupationBudget_le_occupationMeasureBudget
    (d : RandomOccupationMeasureData) :
    d.occupationBudget ≤ randomOccupationMeasureBudget d := by
  unfold randomOccupationMeasureBudget
  omega

def sampleRandomOccupationMeasureData : RandomOccupationMeasureData :=
  { stateCells := 7, occupationBudget := 9, timeSlack := 3 }

example : randomOccupationMeasureReady sampleRandomOccupationMeasureData := by
  norm_num [randomOccupationMeasureReady, stateCellsPositive]
  norm_num [occupationBudgetControlled, sampleRandomOccupationMeasureData]

example : randomOccupationMeasureBudget sampleRandomOccupationMeasureData = 19 := by
  native_decide

/-- Finite executable readiness audit for occupation-measure windows. -/
def randomOccupationMeasureListReady
    (windows : List RandomOccupationMeasureData) : Bool :=
  windows.all fun d =>
    0 < d.stateCells && d.occupationBudget ≤ d.stateCells + d.timeSlack

theorem randomOccupationMeasureList_readyWindow :
    randomOccupationMeasureListReady
      [{ stateCells := 4, occupationBudget := 5, timeSlack := 1 },
       { stateCells := 7, occupationBudget := 9, timeSlack := 3 }] = true := by
  unfold randomOccupationMeasureListReady
  native_decide

structure RandomOccupationMeasureBudgetCertificate where
  stateCellsWindow : ℕ
  occupationBudgetWindow : ℕ
  timeSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomOccupationMeasureBudgetCertificate.controlled
    (c : RandomOccupationMeasureBudgetCertificate) : Prop :=
  0 < c.stateCellsWindow ∧
    c.occupationBudgetWindow ≤ c.stateCellsWindow + c.timeSlackWindow + c.slack

def RandomOccupationMeasureBudgetCertificate.budgetControlled
    (c : RandomOccupationMeasureBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.stateCellsWindow + c.occupationBudgetWindow + c.timeSlackWindow + c.slack

def RandomOccupationMeasureBudgetCertificate.Ready
    (c : RandomOccupationMeasureBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomOccupationMeasureBudgetCertificate.size
    (c : RandomOccupationMeasureBudgetCertificate) : ℕ :=
  c.stateCellsWindow + c.occupationBudgetWindow + c.timeSlackWindow + c.slack

theorem randomOccupationMeasure_budgetCertificate_le_size
    (c : RandomOccupationMeasureBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomOccupationMeasureBudgetCertificate :
    RandomOccupationMeasureBudgetCertificate :=
  { stateCellsWindow := 7
    occupationBudgetWindow := 9
    timeSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomOccupationMeasureBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomOccupationMeasureBudgetCertificate.controlled,
      sampleRandomOccupationMeasureBudgetCertificate]
  · norm_num [RandomOccupationMeasureBudgetCertificate.budgetControlled,
      sampleRandomOccupationMeasureBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomOccupationMeasureBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomOccupationMeasureBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomOccupationMeasureBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomOccupationMeasureBudgetCertificate.controlled,
      sampleRandomOccupationMeasureBudgetCertificate]
  · norm_num [RandomOccupationMeasureBudgetCertificate.budgetControlled,
      sampleRandomOccupationMeasureBudgetCertificate]

example :
    sampleRandomOccupationMeasureBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomOccupationMeasureBudgetCertificate.size := by
  apply randomOccupationMeasure_budgetCertificate_le_size
  constructor
  · norm_num [RandomOccupationMeasureBudgetCertificate.controlled,
      sampleRandomOccupationMeasureBudgetCertificate]
  · norm_num [RandomOccupationMeasureBudgetCertificate.budgetControlled,
      sampleRandomOccupationMeasureBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomOccupationMeasureBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomOccupationMeasureBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomOccupationMeasureBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomOccupationMeasureSchemas
