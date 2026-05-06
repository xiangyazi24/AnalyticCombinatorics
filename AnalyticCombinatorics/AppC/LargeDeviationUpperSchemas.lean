import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Large deviation upper schemas.

The finite record stores rate budget, compact cover budget, and tail
slack for upper-bound templates.
-/

namespace AnalyticCombinatorics.AppC.LargeDeviationUpperSchemas

structure LargeDeviationUpperData where
  rateBudget : ℕ
  compactCoverBudget : ℕ
  tailSlack : ℕ
deriving DecidableEq, Repr

def compactCoverPositive (d : LargeDeviationUpperData) : Prop :=
  0 < d.compactCoverBudget

def rateControlled (d : LargeDeviationUpperData) : Prop :=
  d.rateBudget ≤ d.compactCoverBudget + d.tailSlack

def largeDeviationUpperReady (d : LargeDeviationUpperData) : Prop :=
  compactCoverPositive d ∧ rateControlled d

def largeDeviationUpperBudget (d : LargeDeviationUpperData) : ℕ :=
  d.rateBudget + d.compactCoverBudget + d.tailSlack

theorem largeDeviationUpperReady.cover {d : LargeDeviationUpperData}
    (h : largeDeviationUpperReady d) :
    compactCoverPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem rateBudget_le_largeDeviationUpperBudget
    (d : LargeDeviationUpperData) :
    d.rateBudget ≤ largeDeviationUpperBudget d := by
  unfold largeDeviationUpperBudget
  omega

def sampleLargeDeviationUpperData : LargeDeviationUpperData :=
  { rateBudget := 8, compactCoverBudget := 6, tailSlack := 3 }

example : largeDeviationUpperReady sampleLargeDeviationUpperData := by
  norm_num [largeDeviationUpperReady, compactCoverPositive]
  norm_num [rateControlled, sampleLargeDeviationUpperData]

example : largeDeviationUpperBudget sampleLargeDeviationUpperData = 17 := by
  native_decide

structure LargeDeviationUpperWindow where
  rateWindow : ℕ
  coverWindow : ℕ
  tailSlack : ℕ
  upperBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LargeDeviationUpperWindow.rateControlled (w : LargeDeviationUpperWindow) : Prop :=
  w.rateWindow ≤ w.coverWindow + w.tailSlack + w.slack

def largeDeviationUpperWindowReady (w : LargeDeviationUpperWindow) : Prop :=
  0 < w.coverWindow ∧ w.rateControlled ∧
    w.upperBudget ≤ w.rateWindow + w.coverWindow + w.slack

def LargeDeviationUpperWindow.certificate (w : LargeDeviationUpperWindow) : ℕ :=
  w.rateWindow + w.coverWindow + w.tailSlack + w.upperBudget + w.slack

theorem largeDeviationUpper_upperBudget_le_certificate (w : LargeDeviationUpperWindow) :
    w.upperBudget ≤ w.certificate := by
  unfold LargeDeviationUpperWindow.certificate
  omega

def sampleLargeDeviationUpperWindow : LargeDeviationUpperWindow :=
  { rateWindow := 7, coverWindow := 6, tailSlack := 2, upperBudget := 14, slack := 1 }

example : largeDeviationUpperWindowReady sampleLargeDeviationUpperWindow := by
  norm_num [largeDeviationUpperWindowReady, LargeDeviationUpperWindow.rateControlled,
    sampleLargeDeviationUpperWindow]


structure LargeDeviationUpperSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LargeDeviationUpperSchemasBudgetCertificate.controlled
    (c : LargeDeviationUpperSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LargeDeviationUpperSchemasBudgetCertificate.budgetControlled
    (c : LargeDeviationUpperSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LargeDeviationUpperSchemasBudgetCertificate.Ready
    (c : LargeDeviationUpperSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LargeDeviationUpperSchemasBudgetCertificate.size
    (c : LargeDeviationUpperSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem largeDeviationUpperSchemas_budgetCertificate_le_size
    (c : LargeDeviationUpperSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLargeDeviationUpperSchemasBudgetCertificate :
    LargeDeviationUpperSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLargeDeviationUpperSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LargeDeviationUpperSchemasBudgetCertificate.controlled,
      sampleLargeDeviationUpperSchemasBudgetCertificate]
  · norm_num [LargeDeviationUpperSchemasBudgetCertificate.budgetControlled,
      sampleLargeDeviationUpperSchemasBudgetCertificate]

example : sampleLargeDeviationUpperSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LargeDeviationUpperSchemasBudgetCertificate.controlled,
      sampleLargeDeviationUpperSchemasBudgetCertificate]
  · norm_num [LargeDeviationUpperSchemasBudgetCertificate.budgetControlled,
      sampleLargeDeviationUpperSchemasBudgetCertificate]

example :
    sampleLargeDeviationUpperSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLargeDeviationUpperSchemasBudgetCertificate.size := by
  apply largeDeviationUpperSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LargeDeviationUpperSchemasBudgetCertificate.controlled,
      sampleLargeDeviationUpperSchemasBudgetCertificate]
  · norm_num [LargeDeviationUpperSchemasBudgetCertificate.budgetControlled,
      sampleLargeDeviationUpperSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleLargeDeviationUpperSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLargeDeviationUpperSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LargeDeviationUpperSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLargeDeviationUpperSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLargeDeviationUpperSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.LargeDeviationUpperSchemas
