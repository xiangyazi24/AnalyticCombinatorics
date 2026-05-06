import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Berry--Esseen schemas.

The finite data stores variance scale, third-moment budget, and error
tolerance.
-/

namespace AnalyticCombinatorics.AppC.BerryEsseenSchemas

structure BerryEsseenData where
  varianceScale : ℕ
  thirdMomentBudget : ℕ
  errorTolerance : ℕ
deriving DecidableEq, Repr

def positiveVarianceScale (d : BerryEsseenData) : Prop :=
  0 < d.varianceScale

def thirdMomentControlled (d : BerryEsseenData) : Prop :=
  d.thirdMomentBudget ≤ d.varianceScale + d.errorTolerance

def berryEsseenReady (d : BerryEsseenData) : Prop :=
  positiveVarianceScale d ∧ thirdMomentControlled d

def berryEsseenBudget (d : BerryEsseenData) : ℕ :=
  d.varianceScale + d.thirdMomentBudget + d.errorTolerance

theorem berryEsseenReady.variance {d : BerryEsseenData}
    (h : berryEsseenReady d) :
    positiveVarianceScale d ∧ thirdMomentControlled d ∧
      d.thirdMomentBudget ≤ berryEsseenBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold berryEsseenBudget
  omega

theorem thirdMoment_le_berryEsseenBudget (d : BerryEsseenData) :
    d.thirdMomentBudget ≤ berryEsseenBudget d := by
  unfold berryEsseenBudget
  omega

def sampleBerryEsseenData : BerryEsseenData :=
  { varianceScale := 10, thirdMomentBudget := 12, errorTolerance := 3 }

example : berryEsseenReady sampleBerryEsseenData := by
  norm_num [berryEsseenReady, positiveVarianceScale]
  norm_num [thirdMomentControlled, sampleBerryEsseenData]

example : berryEsseenBudget sampleBerryEsseenData = 25 := by
  native_decide

structure BerryEsseenWindow where
  varianceWindow : ℕ
  thirdMomentWindow : ℕ
  toleranceWindow : ℕ
  approximationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BerryEsseenWindow.thirdMomentControlled (w : BerryEsseenWindow) : Prop :=
  w.thirdMomentWindow ≤ w.varianceWindow + w.toleranceWindow + w.slack

def berryEsseenWindowReady (w : BerryEsseenWindow) : Prop :=
  0 < w.varianceWindow ∧ w.thirdMomentControlled ∧
    w.approximationBudget ≤ w.varianceWindow + w.thirdMomentWindow + w.slack

def BerryEsseenWindow.certificate (w : BerryEsseenWindow) : ℕ :=
  w.varianceWindow + w.thirdMomentWindow + w.toleranceWindow + w.approximationBudget + w.slack

theorem berryEsseen_approximationBudget_le_certificate (w : BerryEsseenWindow) :
    w.approximationBudget ≤ w.certificate := by
  unfold BerryEsseenWindow.certificate
  omega

def sampleBerryEsseenWindow : BerryEsseenWindow :=
  { varianceWindow := 10, thirdMomentWindow := 12, toleranceWindow := 3,
    approximationBudget := 23, slack := 2 }

example : berryEsseenWindowReady sampleBerryEsseenWindow := by
  norm_num [berryEsseenWindowReady, BerryEsseenWindow.thirdMomentControlled,
    sampleBerryEsseenWindow]


structure BerryEsseenSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BerryEsseenSchemasBudgetCertificate.controlled
    (c : BerryEsseenSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BerryEsseenSchemasBudgetCertificate.budgetControlled
    (c : BerryEsseenSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BerryEsseenSchemasBudgetCertificate.Ready
    (c : BerryEsseenSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BerryEsseenSchemasBudgetCertificate.size
    (c : BerryEsseenSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem berryEsseenSchemas_budgetCertificate_le_size
    (c : BerryEsseenSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBerryEsseenSchemasBudgetCertificate :
    BerryEsseenSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBerryEsseenSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BerryEsseenSchemasBudgetCertificate.controlled,
      sampleBerryEsseenSchemasBudgetCertificate]
  · norm_num [BerryEsseenSchemasBudgetCertificate.budgetControlled,
      sampleBerryEsseenSchemasBudgetCertificate]

example : sampleBerryEsseenSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BerryEsseenSchemasBudgetCertificate.controlled,
      sampleBerryEsseenSchemasBudgetCertificate]
  · norm_num [BerryEsseenSchemasBudgetCertificate.budgetControlled,
      sampleBerryEsseenSchemasBudgetCertificate]

example :
    sampleBerryEsseenSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBerryEsseenSchemasBudgetCertificate.size := by
  apply berryEsseenSchemas_budgetCertificate_le_size
  constructor
  · norm_num [BerryEsseenSchemasBudgetCertificate.controlled,
      sampleBerryEsseenSchemasBudgetCertificate]
  · norm_num [BerryEsseenSchemasBudgetCertificate.budgetControlled,
      sampleBerryEsseenSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleBerryEsseenSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBerryEsseenSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BerryEsseenSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBerryEsseenSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBerryEsseenSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.BerryEsseenSchemas
