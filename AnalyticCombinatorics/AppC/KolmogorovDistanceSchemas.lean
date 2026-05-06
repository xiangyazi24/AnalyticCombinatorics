import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Kolmogorov distance schemas.

The finite record packages grid, jump, and tolerance budgets for
distribution-function comparisons.
-/

namespace AnalyticCombinatorics.AppC.KolmogorovDistanceSchemas

structure KolmogorovDistanceData where
  gridPoints : ℕ
  jumpBudget : ℕ
  tolerance : ℕ
deriving DecidableEq, Repr

def gridNonempty (d : KolmogorovDistanceData) : Prop :=
  0 < d.gridPoints

def jumpsControlled (d : KolmogorovDistanceData) : Prop :=
  d.jumpBudget ≤ d.gridPoints + d.tolerance

def kolmogorovDistanceReady (d : KolmogorovDistanceData) : Prop :=
  gridNonempty d ∧ jumpsControlled d

def kolmogorovDistanceBudget (d : KolmogorovDistanceData) : ℕ :=
  d.gridPoints + d.jumpBudget + d.tolerance

theorem kolmogorovDistanceReady.grid {d : KolmogorovDistanceData}
    (h : kolmogorovDistanceReady d) :
    gridNonempty d ∧ jumpsControlled d ∧ d.jumpBudget ≤ kolmogorovDistanceBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold kolmogorovDistanceBudget
  omega

theorem tolerance_le_kolmogorovBudget (d : KolmogorovDistanceData) :
    d.tolerance ≤ kolmogorovDistanceBudget d := by
  unfold kolmogorovDistanceBudget
  omega

def sampleKolmogorovDistanceData : KolmogorovDistanceData :=
  { gridPoints := 8, jumpBudget := 9, tolerance := 2 }

example : kolmogorovDistanceReady sampleKolmogorovDistanceData := by
  norm_num [kolmogorovDistanceReady, gridNonempty]
  norm_num [jumpsControlled, sampleKolmogorovDistanceData]

example : kolmogorovDistanceBudget sampleKolmogorovDistanceData = 19 := by
  native_decide

structure KolmogorovDistanceWindow where
  gridWindow : ℕ
  jumpWindow : ℕ
  toleranceWindow : ℕ
  distanceBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KolmogorovDistanceWindow.jumpsControlled (w : KolmogorovDistanceWindow) : Prop :=
  w.jumpWindow ≤ w.gridWindow + w.toleranceWindow + w.slack

def kolmogorovDistanceWindowReady (w : KolmogorovDistanceWindow) : Prop :=
  0 < w.gridWindow ∧ w.jumpsControlled ∧
    w.distanceBudget ≤ w.gridWindow + w.jumpWindow + w.slack

def KolmogorovDistanceWindow.certificate (w : KolmogorovDistanceWindow) : ℕ :=
  w.gridWindow + w.jumpWindow + w.toleranceWindow + w.distanceBudget + w.slack

theorem kolmogorovDistance_distanceBudget_le_certificate
    (w : KolmogorovDistanceWindow) :
    w.distanceBudget ≤ w.certificate := by
  unfold KolmogorovDistanceWindow.certificate
  omega

def sampleKolmogorovDistanceWindow : KolmogorovDistanceWindow :=
  { gridWindow := 8, jumpWindow := 9, toleranceWindow := 2, distanceBudget := 18, slack := 1 }

example : kolmogorovDistanceWindowReady sampleKolmogorovDistanceWindow := by
  norm_num [kolmogorovDistanceWindowReady, KolmogorovDistanceWindow.jumpsControlled,
    sampleKolmogorovDistanceWindow]


structure KolmogorovDistanceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KolmogorovDistanceSchemasBudgetCertificate.controlled
    (c : KolmogorovDistanceSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def KolmogorovDistanceSchemasBudgetCertificate.budgetControlled
    (c : KolmogorovDistanceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def KolmogorovDistanceSchemasBudgetCertificate.Ready
    (c : KolmogorovDistanceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def KolmogorovDistanceSchemasBudgetCertificate.size
    (c : KolmogorovDistanceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem kolmogorovDistanceSchemas_budgetCertificate_le_size
    (c : KolmogorovDistanceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleKolmogorovDistanceSchemasBudgetCertificate :
    KolmogorovDistanceSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleKolmogorovDistanceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [KolmogorovDistanceSchemasBudgetCertificate.controlled,
      sampleKolmogorovDistanceSchemasBudgetCertificate]
  · norm_num [KolmogorovDistanceSchemasBudgetCertificate.budgetControlled,
      sampleKolmogorovDistanceSchemasBudgetCertificate]

example : sampleKolmogorovDistanceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [KolmogorovDistanceSchemasBudgetCertificate.controlled,
      sampleKolmogorovDistanceSchemasBudgetCertificate]
  · norm_num [KolmogorovDistanceSchemasBudgetCertificate.budgetControlled,
      sampleKolmogorovDistanceSchemasBudgetCertificate]

example :
    sampleKolmogorovDistanceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleKolmogorovDistanceSchemasBudgetCertificate.size := by
  apply kolmogorovDistanceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [KolmogorovDistanceSchemasBudgetCertificate.controlled,
      sampleKolmogorovDistanceSchemasBudgetCertificate]
  · norm_num [KolmogorovDistanceSchemasBudgetCertificate.budgetControlled,
      sampleKolmogorovDistanceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleKolmogorovDistanceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleKolmogorovDistanceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List KolmogorovDistanceSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleKolmogorovDistanceSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleKolmogorovDistanceSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.KolmogorovDistanceSchemas
