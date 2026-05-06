import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite flow models.

The model records source, sink, and edge-capacity budgets for a finite
network abstraction.
-/

namespace AnalyticCombinatorics.AppA.FiniteFlowModels

structure FlowData where
  sourceCapacity : ℕ
  sinkDemand : ℕ
  edgeCapacity : ℕ
deriving DecidableEq, Repr

def sourceAvailable (d : FlowData) : Prop :=
  0 < d.sourceCapacity

def demandControlled (d : FlowData) : Prop :=
  d.sinkDemand ≤ d.sourceCapacity + d.edgeCapacity

def flowReady (d : FlowData) : Prop :=
  sourceAvailable d ∧ demandControlled d

def flowBudget (d : FlowData) : ℕ :=
  d.sourceCapacity + d.sinkDemand + d.edgeCapacity

theorem flowReady.source {d : FlowData} (h : flowReady d) :
    sourceAvailable d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem sinkDemand_le_flowBudget (d : FlowData) :
    d.sinkDemand ≤ flowBudget d := by
  unfold flowBudget
  omega

def sampleFlowData : FlowData :=
  { sourceCapacity := 6, sinkDemand := 8, edgeCapacity := 4 }

example : flowReady sampleFlowData := by
  norm_num [flowReady, sourceAvailable]
  norm_num [demandControlled, sampleFlowData]

example : flowBudget sampleFlowData = 18 := by
  native_decide

structure FlowWindow where
  sourceCapacity : ℕ
  sinkDemand : ℕ
  edgeCapacity : ℕ
  routedFlow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FlowWindow.sourceReady (w : FlowWindow) : Prop :=
  0 < w.sourceCapacity

def FlowWindow.demandControlled (w : FlowWindow) : Prop :=
  w.sinkDemand ≤ w.sourceCapacity + w.edgeCapacity + w.slack

def FlowWindow.routedControlled (w : FlowWindow) : Prop :=
  w.routedFlow ≤ w.sourceCapacity + w.edgeCapacity + w.slack

def FlowWindow.ready (w : FlowWindow) : Prop :=
  w.sourceReady ∧ w.demandControlled ∧ w.routedControlled

def FlowWindow.certificate (w : FlowWindow) : ℕ :=
  w.sourceCapacity + w.sinkDemand + w.edgeCapacity + w.routedFlow + w.slack

theorem routedFlow_le_certificate (w : FlowWindow) :
    w.routedFlow ≤ w.certificate := by
  unfold FlowWindow.certificate
  omega

def sampleFlowWindow : FlowWindow :=
  { sourceCapacity := 6, sinkDemand := 8, edgeCapacity := 4, routedFlow := 7, slack := 0 }

example : sampleFlowWindow.ready := by
  norm_num [sampleFlowWindow, FlowWindow.ready, FlowWindow.sourceReady,
    FlowWindow.demandControlled, FlowWindow.routedControlled]


structure FiniteFlowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteFlowModelsBudgetCertificate.controlled
    (c : FiniteFlowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteFlowModelsBudgetCertificate.budgetControlled
    (c : FiniteFlowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteFlowModelsBudgetCertificate.Ready
    (c : FiniteFlowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteFlowModelsBudgetCertificate.size
    (c : FiniteFlowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteFlowModels_budgetCertificate_le_size
    (c : FiniteFlowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteFlowModelsBudgetCertificate :
    FiniteFlowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteFlowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteFlowModelsBudgetCertificate.controlled,
      sampleFiniteFlowModelsBudgetCertificate]
  · norm_num [FiniteFlowModelsBudgetCertificate.budgetControlled,
      sampleFiniteFlowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteFlowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteFlowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteFlowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteFlowModelsBudgetCertificate.controlled,
      sampleFiniteFlowModelsBudgetCertificate]
  · norm_num [FiniteFlowModelsBudgetCertificate.budgetControlled,
      sampleFiniteFlowModelsBudgetCertificate]

example :
    sampleFiniteFlowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteFlowModelsBudgetCertificate.size := by
  apply finiteFlowModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteFlowModelsBudgetCertificate.controlled,
      sampleFiniteFlowModelsBudgetCertificate]
  · norm_num [FiniteFlowModelsBudgetCertificate.budgetControlled,
      sampleFiniteFlowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteFlowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteFlowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteFlowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteFlowModels
