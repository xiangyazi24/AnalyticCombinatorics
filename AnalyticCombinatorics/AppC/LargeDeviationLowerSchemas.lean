import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Large deviation lower schemas.

The finite record stores local rate budget, neighborhood budget, and
exponential slack for lower-bound templates.
-/

namespace AnalyticCombinatorics.AppC.LargeDeviationLowerSchemas

structure LargeDeviationLowerData where
  localRateBudget : ℕ
  neighborhoodBudget : ℕ
  exponentialSlack : ℕ
deriving DecidableEq, Repr

def neighborhoodBudgetPositive (d : LargeDeviationLowerData) : Prop :=
  0 < d.neighborhoodBudget

def localRateControlled (d : LargeDeviationLowerData) : Prop :=
  d.localRateBudget ≤ d.neighborhoodBudget + d.exponentialSlack

def largeDeviationLowerReady (d : LargeDeviationLowerData) : Prop :=
  neighborhoodBudgetPositive d ∧ localRateControlled d

def largeDeviationLowerBudget (d : LargeDeviationLowerData) : ℕ :=
  d.localRateBudget + d.neighborhoodBudget + d.exponentialSlack

theorem largeDeviationLowerReady.neighborhood
    {d : LargeDeviationLowerData}
    (h : largeDeviationLowerReady d) :
    neighborhoodBudgetPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem localRate_le_largeDeviationLowerBudget
    (d : LargeDeviationLowerData) :
    d.localRateBudget ≤ largeDeviationLowerBudget d := by
  unfold largeDeviationLowerBudget
  omega

def sampleLargeDeviationLowerData : LargeDeviationLowerData :=
  { localRateBudget := 7, neighborhoodBudget := 5, exponentialSlack := 3 }

example : largeDeviationLowerReady sampleLargeDeviationLowerData := by
  norm_num [largeDeviationLowerReady, neighborhoodBudgetPositive]
  norm_num [localRateControlled, sampleLargeDeviationLowerData]

example : largeDeviationLowerBudget sampleLargeDeviationLowerData = 15 := by
  native_decide

structure LargeDeviationLowerWindow where
  rateWindow : ℕ
  neighborhoodWindow : ℕ
  exponentialSlack : ℕ
  lowerBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LargeDeviationLowerWindow.rateControlled (w : LargeDeviationLowerWindow) : Prop :=
  w.rateWindow ≤ w.neighborhoodWindow + w.exponentialSlack + w.slack

def largeDeviationLowerWindowReady (w : LargeDeviationLowerWindow) : Prop :=
  0 < w.neighborhoodWindow ∧ w.rateControlled ∧
    w.lowerBudget ≤ w.rateWindow + w.neighborhoodWindow + w.slack

def LargeDeviationLowerWindow.certificate (w : LargeDeviationLowerWindow) : ℕ :=
  w.rateWindow + w.neighborhoodWindow + w.exponentialSlack + w.lowerBudget + w.slack

theorem largeDeviationLower_lowerBudget_le_certificate
    (w : LargeDeviationLowerWindow) :
    w.lowerBudget ≤ w.certificate := by
  unfold LargeDeviationLowerWindow.certificate
  omega

def sampleLargeDeviationLowerWindow : LargeDeviationLowerWindow :=
  { rateWindow := 6, neighborhoodWindow := 5, exponentialSlack := 2,
    lowerBudget := 12, slack := 1 }

example : largeDeviationLowerWindowReady sampleLargeDeviationLowerWindow := by
  norm_num [largeDeviationLowerWindowReady, LargeDeviationLowerWindow.rateControlled,
    sampleLargeDeviationLowerWindow]


structure LargeDeviationLowerSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LargeDeviationLowerSchemasBudgetCertificate.controlled
    (c : LargeDeviationLowerSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LargeDeviationLowerSchemasBudgetCertificate.budgetControlled
    (c : LargeDeviationLowerSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LargeDeviationLowerSchemasBudgetCertificate.Ready
    (c : LargeDeviationLowerSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LargeDeviationLowerSchemasBudgetCertificate.size
    (c : LargeDeviationLowerSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem largeDeviationLowerSchemas_budgetCertificate_le_size
    (c : LargeDeviationLowerSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLargeDeviationLowerSchemasBudgetCertificate :
    LargeDeviationLowerSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLargeDeviationLowerSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LargeDeviationLowerSchemasBudgetCertificate.controlled,
      sampleLargeDeviationLowerSchemasBudgetCertificate]
  · norm_num [LargeDeviationLowerSchemasBudgetCertificate.budgetControlled,
      sampleLargeDeviationLowerSchemasBudgetCertificate]

example : sampleLargeDeviationLowerSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LargeDeviationLowerSchemasBudgetCertificate.controlled,
      sampleLargeDeviationLowerSchemasBudgetCertificate]
  · norm_num [LargeDeviationLowerSchemasBudgetCertificate.budgetControlled,
      sampleLargeDeviationLowerSchemasBudgetCertificate]

example :
    sampleLargeDeviationLowerSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLargeDeviationLowerSchemasBudgetCertificate.size := by
  apply largeDeviationLowerSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LargeDeviationLowerSchemasBudgetCertificate.controlled,
      sampleLargeDeviationLowerSchemasBudgetCertificate]
  · norm_num [LargeDeviationLowerSchemasBudgetCertificate.budgetControlled,
      sampleLargeDeviationLowerSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleLargeDeviationLowerSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLargeDeviationLowerSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LargeDeviationLowerSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLargeDeviationLowerSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLargeDeviationLowerSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.LargeDeviationLowerSchemas
