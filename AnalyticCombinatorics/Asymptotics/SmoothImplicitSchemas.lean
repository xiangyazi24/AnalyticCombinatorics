import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Smooth implicit schemas.

The finite abstraction records smoothness order, Jacobian clearance, and
remainder budget.
-/

namespace AnalyticCombinatorics.Asymptotics.SmoothImplicitSchemas

structure SmoothImplicitData where
  smoothnessOrder : ℕ
  jacobianClearance : ℕ
  remainderBudget : ℕ
deriving DecidableEq, Repr

def jacobianClearancePositive (d : SmoothImplicitData) : Prop :=
  0 < d.jacobianClearance

def smoothnessControlled (d : SmoothImplicitData) : Prop :=
  d.smoothnessOrder ≤ d.jacobianClearance + d.remainderBudget

def smoothImplicitReady (d : SmoothImplicitData) : Prop :=
  jacobianClearancePositive d ∧ smoothnessControlled d

def smoothImplicitBudget (d : SmoothImplicitData) : ℕ :=
  d.smoothnessOrder + d.jacobianClearance + d.remainderBudget

theorem smoothImplicitReady.jacobian {d : SmoothImplicitData}
    (h : smoothImplicitReady d) :
    jacobianClearancePositive d ∧ smoothnessControlled d ∧
      d.smoothnessOrder ≤ smoothImplicitBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold smoothImplicitBudget
  omega

theorem smoothnessOrder_le_smoothImplicitBudget (d : SmoothImplicitData) :
    d.smoothnessOrder ≤ smoothImplicitBudget d := by
  unfold smoothImplicitBudget
  omega

def sampleSmoothImplicitData : SmoothImplicitData :=
  { smoothnessOrder := 6, jacobianClearance := 4, remainderBudget := 5 }

example : smoothImplicitReady sampleSmoothImplicitData := by
  norm_num [smoothImplicitReady, jacobianClearancePositive]
  norm_num [smoothnessControlled, sampleSmoothImplicitData]

example : smoothImplicitBudget sampleSmoothImplicitData = 15 := by
  native_decide

/-- Finite executable readiness audit for smooth implicit data. -/
def smoothImplicitDataListReady
    (data : List SmoothImplicitData) : Bool :=
  data.all fun d =>
    0 < d.jacobianClearance &&
      d.smoothnessOrder ≤ d.jacobianClearance + d.remainderBudget

theorem smoothImplicitDataList_readyWindow :
    smoothImplicitDataListReady
      [{ smoothnessOrder := 3, jacobianClearance := 2, remainderBudget := 2 },
       { smoothnessOrder := 6, jacobianClearance := 4, remainderBudget := 5 }] =
      true := by
  unfold smoothImplicitDataListReady
  native_decide

/-- A certificate window for smooth implicit schema control. -/
structure SmoothImplicitCertificateWindow where
  smoothnessWindow : ℕ
  jacobianWindow : ℕ
  remainderWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Smoothness is controlled by Jacobian clearance and remainder slack. -/
def smoothImplicitCertificateControlled
    (w : SmoothImplicitCertificateWindow) : Prop :=
  w.smoothnessWindow ≤ w.jacobianWindow + w.remainderWindow + w.slack

/-- Readiness for a smooth implicit certificate. -/
def smoothImplicitCertificateReady
    (w : SmoothImplicitCertificateWindow) : Prop :=
  0 < w.jacobianWindow ∧
    smoothImplicitCertificateControlled w ∧
      w.certificateBudget ≤
        w.smoothnessWindow + w.jacobianWindow + w.remainderWindow + w.slack

/-- Total size of a smooth implicit certificate. -/
def smoothImplicitCertificate (w : SmoothImplicitCertificateWindow) : ℕ :=
  w.smoothnessWindow + w.jacobianWindow + w.remainderWindow +
    w.certificateBudget + w.slack

theorem smoothImplicitCertificate_budget_le_certificate
    (w : SmoothImplicitCertificateWindow)
    (h : smoothImplicitCertificateReady w) :
    w.certificateBudget ≤ smoothImplicitCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold smoothImplicitCertificate
  omega

def sampleSmoothImplicitCertificateWindow :
    SmoothImplicitCertificateWindow where
  smoothnessWindow := 7
  jacobianWindow := 5
  remainderWindow := 4
  certificateBudget := 15
  slack := 1

example :
    smoothImplicitCertificateReady sampleSmoothImplicitCertificateWindow := by
  norm_num [smoothImplicitCertificateReady,
    smoothImplicitCertificateControlled, sampleSmoothImplicitCertificateWindow]

example :
    sampleSmoothImplicitCertificateWindow.certificateBudget ≤
      smoothImplicitCertificate sampleSmoothImplicitCertificateWindow := by
  apply smoothImplicitCertificate_budget_le_certificate
  norm_num [smoothImplicitCertificateReady,
    smoothImplicitCertificateControlled, sampleSmoothImplicitCertificateWindow]

structure SmoothImplicitRefinementCertificate where
  smoothnessWindow : ℕ
  jacobianWindow : ℕ
  remainderWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SmoothImplicitRefinementCertificate.smoothnessControlled
    (c : SmoothImplicitRefinementCertificate) : Prop :=
  c.smoothnessWindow ≤ c.jacobianWindow + c.remainderWindow + c.slack

def SmoothImplicitRefinementCertificate.certificateBudgetControlled
    (c : SmoothImplicitRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.smoothnessWindow + c.jacobianWindow + c.remainderWindow + c.slack

def smoothImplicitRefinementReady
    (c : SmoothImplicitRefinementCertificate) : Prop :=
  0 < c.jacobianWindow ∧
    c.smoothnessControlled ∧
    c.certificateBudgetControlled

def SmoothImplicitRefinementCertificate.size
    (c : SmoothImplicitRefinementCertificate) : ℕ :=
  c.smoothnessWindow + c.jacobianWindow + c.remainderWindow + c.slack

theorem smoothImplicit_certificateBudgetWindow_le_size
    {c : SmoothImplicitRefinementCertificate}
    (h : smoothImplicitRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleSmoothImplicitRefinementCertificate :
    SmoothImplicitRefinementCertificate :=
  { smoothnessWindow := 7, jacobianWindow := 5, remainderWindow := 4,
    certificateBudgetWindow := 17, slack := 1 }

example : smoothImplicitRefinementReady
    sampleSmoothImplicitRefinementCertificate := by
  norm_num [smoothImplicitRefinementReady,
    SmoothImplicitRefinementCertificate.smoothnessControlled,
    SmoothImplicitRefinementCertificate.certificateBudgetControlled,
    sampleSmoothImplicitRefinementCertificate]

example :
    sampleSmoothImplicitRefinementCertificate.certificateBudgetWindow ≤
      sampleSmoothImplicitRefinementCertificate.size := by
  norm_num [SmoothImplicitRefinementCertificate.size,
    sampleSmoothImplicitRefinementCertificate]

structure SmoothImplicitBudgetCertificate where
  smoothnessWindow : ℕ
  jacobianWindow : ℕ
  remainderWindow : ℕ
  smoothBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SmoothImplicitBudgetCertificate.controlled
    (c : SmoothImplicitBudgetCertificate) : Prop :=
  0 < c.jacobianWindow ∧
    c.smoothnessWindow ≤ c.jacobianWindow + c.remainderWindow + c.slack ∧
      c.smoothBudgetWindow ≤
        c.smoothnessWindow + c.jacobianWindow + c.remainderWindow + c.slack

def SmoothImplicitBudgetCertificate.budgetControlled
    (c : SmoothImplicitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.smoothnessWindow + c.jacobianWindow + c.remainderWindow +
      c.smoothBudgetWindow + c.slack

def SmoothImplicitBudgetCertificate.Ready
    (c : SmoothImplicitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SmoothImplicitBudgetCertificate.size
    (c : SmoothImplicitBudgetCertificate) : ℕ :=
  c.smoothnessWindow + c.jacobianWindow + c.remainderWindow +
    c.smoothBudgetWindow + c.slack

theorem smoothImplicit_budgetCertificate_le_size
    (c : SmoothImplicitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSmoothImplicitBudgetCertificate :
    SmoothImplicitBudgetCertificate :=
  { smoothnessWindow := 7
    jacobianWindow := 5
    remainderWindow := 4
    smoothBudgetWindow := 17
    certificateBudgetWindow := 34
    slack := 1 }

example : sampleSmoothImplicitBudgetCertificate.Ready := by
  constructor
  · norm_num [SmoothImplicitBudgetCertificate.controlled,
      sampleSmoothImplicitBudgetCertificate]
  · norm_num [SmoothImplicitBudgetCertificate.budgetControlled,
      sampleSmoothImplicitBudgetCertificate]

example :
    sampleSmoothImplicitBudgetCertificate.certificateBudgetWindow ≤
      sampleSmoothImplicitBudgetCertificate.size := by
  apply smoothImplicit_budgetCertificate_le_size
  constructor
  · norm_num [SmoothImplicitBudgetCertificate.controlled,
      sampleSmoothImplicitBudgetCertificate]
  · norm_num [SmoothImplicitBudgetCertificate.budgetControlled,
      sampleSmoothImplicitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSmoothImplicitBudgetCertificate.Ready := by
  constructor
  · norm_num [SmoothImplicitBudgetCertificate.controlled,
      sampleSmoothImplicitBudgetCertificate]
  · norm_num [SmoothImplicitBudgetCertificate.budgetControlled,
      sampleSmoothImplicitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSmoothImplicitBudgetCertificate.certificateBudgetWindow ≤
      sampleSmoothImplicitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SmoothImplicitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSmoothImplicitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSmoothImplicitBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SmoothImplicitSchemas
