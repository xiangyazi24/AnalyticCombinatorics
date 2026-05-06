import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Turning-point schema bookkeeping.

The record stores turning order, local scale, and Airy-type remainder budget.
-/

namespace AnalyticCombinatorics.Asymptotics.TurningPointSchemas

structure TurningPointData where
  turningOrder : ℕ
  localScale : ℕ
  remainderBudget : ℕ
deriving DecidableEq, Repr

def positiveTurningOrder (d : TurningPointData) : Prop :=
  0 < d.turningOrder

def positiveLocalScale (d : TurningPointData) : Prop :=
  0 < d.localScale

def turningPointReady (d : TurningPointData) : Prop :=
  positiveTurningOrder d ∧ positiveLocalScale d

def turningPointBudget (d : TurningPointData) : ℕ :=
  d.turningOrder * d.localScale + d.remainderBudget

theorem turningPointReady.scale {d : TurningPointData}
    (h : turningPointReady d) :
    positiveTurningOrder d ∧ positiveLocalScale d ∧ d.remainderBudget ≤ turningPointBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold turningPointBudget
  omega

theorem remainder_le_budget (d : TurningPointData) :
    d.remainderBudget ≤ turningPointBudget d := by
  unfold turningPointBudget
  omega

def sampleTurningPoint : TurningPointData :=
  { turningOrder := 3, localScale := 5, remainderBudget := 2 }

example : turningPointReady sampleTurningPoint := by
  norm_num [turningPointReady, positiveTurningOrder, positiveLocalScale, sampleTurningPoint]

example : turningPointBudget sampleTurningPoint = 17 := by
  native_decide

/-- Finite executable readiness audit for turning point data. -/
def turningPointDataListReady (data : List TurningPointData) : Bool :=
  data.all fun d => 0 < d.turningOrder && 0 < d.localScale

theorem turningPointDataList_readyWindow :
    turningPointDataListReady
      [{ turningOrder := 2, localScale := 3, remainderBudget := 1 },
       { turningOrder := 3, localScale := 5, remainderBudget := 2 }] = true := by
  unfold turningPointDataListReady
  native_decide

structure TurningPointWindow where
  turningOrder : ℕ
  localScale : ℕ
  remainderBudget : ℕ
  transitionMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TurningPointWindow.scaleReady (w : TurningPointWindow) : Prop :=
  0 < w.turningOrder ∧ 0 < w.localScale

def TurningPointWindow.remainderControlled (w : TurningPointWindow) : Prop :=
  w.remainderBudget ≤ w.turningOrder * w.localScale + w.slack

def TurningPointWindow.transitionControlled (w : TurningPointWindow) : Prop :=
  w.transitionMass ≤ w.turningOrder * w.localScale + w.remainderBudget + w.slack

def TurningPointWindow.ready (w : TurningPointWindow) : Prop :=
  w.scaleReady ∧ w.remainderControlled ∧ w.transitionControlled

def TurningPointWindow.certificate (w : TurningPointWindow) : ℕ :=
  w.turningOrder + w.localScale + w.remainderBudget + w.transitionMass + w.slack

theorem transitionMass_le_certificate (w : TurningPointWindow) :
    w.transitionMass ≤ w.certificate := by
  unfold TurningPointWindow.certificate
  omega

def sampleTurningPointWindow : TurningPointWindow :=
  { turningOrder := 3, localScale := 5, remainderBudget := 2, transitionMass := 12, slack := 0 }

example : sampleTurningPointWindow.ready := by
  norm_num [sampleTurningPointWindow, TurningPointWindow.ready,
    TurningPointWindow.scaleReady, TurningPointWindow.remainderControlled,
    TurningPointWindow.transitionControlled]

/-- A refinement certificate for turning-point windows. -/
structure TurningPointCertificate where
  turningWindow : ℕ
  scaleWindow : ℕ
  remainderWindow : ℕ
  transitionWindow : ℕ
  slack : ℕ

/-- Turning order and local scale control the remainder and transition mass. -/
def turningPointCertificateControlled
    (w : TurningPointCertificate) : Prop :=
  0 < w.turningWindow ∧
    0 < w.scaleWindow ∧
      w.remainderWindow ≤ w.turningWindow * w.scaleWindow + w.slack ∧
        w.transitionWindow ≤
          w.turningWindow * w.scaleWindow + w.remainderWindow + w.slack

/-- Readiness for a turning-point certificate. -/
def turningPointCertificateReady
    (w : TurningPointCertificate) : Prop :=
  turningPointCertificateControlled w ∧
    w.transitionWindow ≤
      w.turningWindow + w.scaleWindow + w.remainderWindow +
        w.transitionWindow + w.slack

/-- Total size of a turning-point certificate. -/
def turningPointCertificateSize (w : TurningPointCertificate) : ℕ :=
  w.turningWindow + w.scaleWindow + w.remainderWindow + w.transitionWindow + w.slack

theorem turningPointCertificate_transition_le_size
    (w : TurningPointCertificate)
    (h : turningPointCertificateReady w) :
    w.transitionWindow ≤ turningPointCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold turningPointCertificateSize
  omega

def sampleTurningPointCertificate : TurningPointCertificate where
  turningWindow := 3
  scaleWindow := 5
  remainderWindow := 2
  transitionWindow := 12
  slack := 0

example :
    turningPointCertificateReady sampleTurningPointCertificate := by
  norm_num [turningPointCertificateReady,
    turningPointCertificateControlled, sampleTurningPointCertificate]

example :
    sampleTurningPointCertificate.transitionWindow ≤
      turningPointCertificateSize sampleTurningPointCertificate := by
  apply turningPointCertificate_transition_le_size
  norm_num [turningPointCertificateReady,
    turningPointCertificateControlled, sampleTurningPointCertificate]

/-- A refinement certificate with the turning-point budget separated from size. -/
structure TurningPointRefinementCertificate where
  turningWindow : ℕ
  scaleWindow : ℕ
  remainderWindow : ℕ
  transitionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TurningPointRefinementCertificate.turningControlled
    (cert : TurningPointRefinementCertificate) : Prop :=
  0 < cert.turningWindow ∧
    0 < cert.scaleWindow ∧
      cert.remainderWindow ≤ cert.turningWindow * cert.scaleWindow + cert.slack ∧
        cert.transitionWindow ≤
          cert.turningWindow * cert.scaleWindow + cert.remainderWindow + cert.slack

def TurningPointRefinementCertificate.budgetControlled
    (cert : TurningPointRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.turningWindow + cert.scaleWindow + cert.remainderWindow +
      cert.transitionWindow + cert.slack

def turningPointRefinementReady
    (cert : TurningPointRefinementCertificate) : Prop :=
  cert.turningControlled ∧ cert.budgetControlled

def TurningPointRefinementCertificate.size
    (cert : TurningPointRefinementCertificate) : ℕ :=
  cert.turningWindow + cert.scaleWindow + cert.remainderWindow +
    cert.transitionWindow + cert.slack

theorem turningPoint_certificateBudgetWindow_le_size
    (cert : TurningPointRefinementCertificate)
    (h : turningPointRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTurningPointRefinementCertificate :
    TurningPointRefinementCertificate :=
  { turningWindow := 3, scaleWindow := 5, remainderWindow := 2,
    transitionWindow := 12, certificateBudgetWindow := 22, slack := 0 }

example :
    turningPointRefinementReady sampleTurningPointRefinementCertificate := by
  norm_num [turningPointRefinementReady,
    TurningPointRefinementCertificate.turningControlled,
    TurningPointRefinementCertificate.budgetControlled,
    sampleTurningPointRefinementCertificate]

example :
    sampleTurningPointRefinementCertificate.certificateBudgetWindow ≤
      sampleTurningPointRefinementCertificate.size := by
  apply turningPoint_certificateBudgetWindow_le_size
  norm_num [turningPointRefinementReady,
    TurningPointRefinementCertificate.turningControlled,
    TurningPointRefinementCertificate.budgetControlled,
    sampleTurningPointRefinementCertificate]


structure TurningPointSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TurningPointSchemasBudgetCertificate.controlled
    (c : TurningPointSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def TurningPointSchemasBudgetCertificate.budgetControlled
    (c : TurningPointSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TurningPointSchemasBudgetCertificate.Ready
    (c : TurningPointSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TurningPointSchemasBudgetCertificate.size
    (c : TurningPointSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem turningPointSchemas_budgetCertificate_le_size
    (c : TurningPointSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTurningPointSchemasBudgetCertificate :
    TurningPointSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleTurningPointSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TurningPointSchemasBudgetCertificate.controlled,
      sampleTurningPointSchemasBudgetCertificate]
  · norm_num [TurningPointSchemasBudgetCertificate.budgetControlled,
      sampleTurningPointSchemasBudgetCertificate]

example :
    sampleTurningPointSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTurningPointSchemasBudgetCertificate.size := by
  apply turningPointSchemas_budgetCertificate_le_size
  constructor
  · norm_num [TurningPointSchemasBudgetCertificate.controlled,
      sampleTurningPointSchemasBudgetCertificate]
  · norm_num [TurningPointSchemasBudgetCertificate.budgetControlled,
      sampleTurningPointSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTurningPointSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TurningPointSchemasBudgetCertificate.controlled,
      sampleTurningPointSchemasBudgetCertificate]
  · norm_num [TurningPointSchemasBudgetCertificate.budgetControlled,
      sampleTurningPointSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTurningPointSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTurningPointSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List TurningPointSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTurningPointSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleTurningPointSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.TurningPointSchemas
