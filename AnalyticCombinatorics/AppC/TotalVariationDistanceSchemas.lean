import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Total variation distance schemas.

The finite record tracks partition cells, discrepancy budget, and
smoothing slack.
-/

namespace AnalyticCombinatorics.AppC.TotalVariationDistanceSchemas

structure TotalVariationDistanceData where
  partitionCells : ℕ
  discrepancyBudget : ℕ
  smoothingSlack : ℕ
deriving DecidableEq, Repr

def partitionNonempty (d : TotalVariationDistanceData) : Prop :=
  0 < d.partitionCells

def discrepancyControlled (d : TotalVariationDistanceData) : Prop :=
  d.discrepancyBudget ≤ d.partitionCells + d.smoothingSlack

def totalVariationDistanceReady (d : TotalVariationDistanceData) : Prop :=
  partitionNonempty d ∧ discrepancyControlled d

def totalVariationDistanceBudget (d : TotalVariationDistanceData) : ℕ :=
  d.partitionCells + d.discrepancyBudget + d.smoothingSlack

theorem totalVariationDistanceReady.partition
    {d : TotalVariationDistanceData}
    (h : totalVariationDistanceReady d) :
    partitionNonempty d ∧ discrepancyControlled d ∧
      d.discrepancyBudget ≤ totalVariationDistanceBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold totalVariationDistanceBudget
  omega

theorem partitionCells_le_totalVariationBudget
    (d : TotalVariationDistanceData) :
    d.partitionCells ≤ totalVariationDistanceBudget d := by
  unfold totalVariationDistanceBudget
  omega

def sampleTotalVariationDistanceData : TotalVariationDistanceData :=
  { partitionCells := 7, discrepancyBudget := 9, smoothingSlack := 4 }

example : totalVariationDistanceReady sampleTotalVariationDistanceData := by
  norm_num [totalVariationDistanceReady, partitionNonempty]
  norm_num [discrepancyControlled, sampleTotalVariationDistanceData]

example :
    totalVariationDistanceBudget sampleTotalVariationDistanceData = 20 := by
  native_decide

structure TotalVariationDistanceWindow where
  partitionWindow : ℕ
  discrepancyWindow : ℕ
  smoothingSlack : ℕ
  distanceBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TotalVariationDistanceWindow.discrepancyControlled
    (w : TotalVariationDistanceWindow) : Prop :=
  w.discrepancyWindow ≤ w.partitionWindow + w.smoothingSlack + w.slack

def totalVariationDistanceWindowReady
    (w : TotalVariationDistanceWindow) : Prop :=
  0 < w.partitionWindow ∧ w.discrepancyControlled ∧
    w.distanceBudget ≤ w.partitionWindow + w.discrepancyWindow + w.slack

def TotalVariationDistanceWindow.certificate
    (w : TotalVariationDistanceWindow) : ℕ :=
  w.partitionWindow + w.discrepancyWindow + w.smoothingSlack + w.distanceBudget + w.slack

theorem totalVariationDistance_distanceBudget_le_certificate
    (w : TotalVariationDistanceWindow) :
    w.distanceBudget ≤ w.certificate := by
  unfold TotalVariationDistanceWindow.certificate
  omega

def sampleTotalVariationDistanceWindow : TotalVariationDistanceWindow :=
  { partitionWindow := 6, discrepancyWindow := 8, smoothingSlack := 3,
    distanceBudget := 15, slack := 1 }

example : totalVariationDistanceWindowReady
    sampleTotalVariationDistanceWindow := by
  norm_num [totalVariationDistanceWindowReady,
    TotalVariationDistanceWindow.discrepancyControlled, sampleTotalVariationDistanceWindow]


structure TotalVariationDistanceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TotalVariationDistanceSchemasBudgetCertificate.controlled
    (c : TotalVariationDistanceSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TotalVariationDistanceSchemasBudgetCertificate.budgetControlled
    (c : TotalVariationDistanceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TotalVariationDistanceSchemasBudgetCertificate.Ready
    (c : TotalVariationDistanceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TotalVariationDistanceSchemasBudgetCertificate.size
    (c : TotalVariationDistanceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem totalVariationDistanceSchemas_budgetCertificate_le_size
    (c : TotalVariationDistanceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTotalVariationDistanceSchemasBudgetCertificate :
    TotalVariationDistanceSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTotalVariationDistanceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TotalVariationDistanceSchemasBudgetCertificate.controlled,
      sampleTotalVariationDistanceSchemasBudgetCertificate]
  · norm_num [TotalVariationDistanceSchemasBudgetCertificate.budgetControlled,
      sampleTotalVariationDistanceSchemasBudgetCertificate]

example : sampleTotalVariationDistanceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TotalVariationDistanceSchemasBudgetCertificate.controlled,
      sampleTotalVariationDistanceSchemasBudgetCertificate]
  · norm_num [TotalVariationDistanceSchemasBudgetCertificate.budgetControlled,
      sampleTotalVariationDistanceSchemasBudgetCertificate]

example :
    sampleTotalVariationDistanceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTotalVariationDistanceSchemasBudgetCertificate.size := by
  apply totalVariationDistanceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [TotalVariationDistanceSchemasBudgetCertificate.controlled,
      sampleTotalVariationDistanceSchemasBudgetCertificate]
  · norm_num [TotalVariationDistanceSchemasBudgetCertificate.budgetControlled,
      sampleTotalVariationDistanceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleTotalVariationDistanceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTotalVariationDistanceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List TotalVariationDistanceSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTotalVariationDistanceSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTotalVariationDistanceSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.TotalVariationDistanceSchemas
