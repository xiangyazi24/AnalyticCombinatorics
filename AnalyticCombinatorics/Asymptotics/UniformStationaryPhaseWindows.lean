import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform stationary phase windows.

This module records finite bookkeeping for stationary phase windows.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformStationaryPhaseWindows

structure StationaryPhaseWindowData where
  phaseOrder : ℕ
  oscillationWindow : ℕ
  phaseSlack : ℕ
deriving DecidableEq, Repr

def hasPhaseOrder (d : StationaryPhaseWindowData) : Prop :=
  0 < d.phaseOrder

def oscillationWindowControlled (d : StationaryPhaseWindowData) : Prop :=
  d.oscillationWindow ≤ d.phaseOrder + d.phaseSlack

def stationaryPhaseReady (d : StationaryPhaseWindowData) : Prop :=
  hasPhaseOrder d ∧ oscillationWindowControlled d

def stationaryPhaseBudget (d : StationaryPhaseWindowData) : ℕ :=
  d.phaseOrder + d.oscillationWindow + d.phaseSlack

theorem stationaryPhaseReady.hasPhaseOrder
    {d : StationaryPhaseWindowData}
    (h : stationaryPhaseReady d) :
    hasPhaseOrder d ∧ oscillationWindowControlled d ∧
      d.oscillationWindow ≤ stationaryPhaseBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold stationaryPhaseBudget
  omega

theorem oscillationWindow_le_budget (d : StationaryPhaseWindowData) :
    d.oscillationWindow ≤ stationaryPhaseBudget d := by
  unfold stationaryPhaseBudget
  omega

def sampleStationaryPhaseWindowData : StationaryPhaseWindowData :=
  { phaseOrder := 7, oscillationWindow := 9, phaseSlack := 3 }

example : stationaryPhaseReady sampleStationaryPhaseWindowData := by
  norm_num [stationaryPhaseReady, hasPhaseOrder]
  norm_num [oscillationWindowControlled, sampleStationaryPhaseWindowData]

example : stationaryPhaseBudget sampleStationaryPhaseWindowData = 19 := by
  native_decide

/-- Finite executable readiness audit for stationary phase windows. -/
def stationaryPhaseWindowDataListReady
    (data : List StationaryPhaseWindowData) : Bool :=
  data.all fun d =>
    0 < d.phaseOrder && d.oscillationWindow ≤ d.phaseOrder + d.phaseSlack

theorem stationaryPhaseWindowDataList_readyWindow :
    stationaryPhaseWindowDataListReady
      [{ phaseOrder := 4, oscillationWindow := 5, phaseSlack := 1 },
       { phaseOrder := 7, oscillationWindow := 9, phaseSlack := 3 }] = true := by
  unfold stationaryPhaseWindowDataListReady
  native_decide

/-- A certificate window for uniform stationary phase. -/
structure StationaryPhaseCertificateWindow where
  phaseWindow : ℕ
  oscillationWindow : ℕ
  phaseSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The oscillation window is controlled by the phase window. -/
def stationaryPhaseCertificateControlled
    (w : StationaryPhaseCertificateWindow) : Prop :=
  w.oscillationWindow ≤ w.phaseWindow + w.phaseSlack + w.slack

/-- Readiness for a stationary phase certificate. -/
def stationaryPhaseCertificateReady
    (w : StationaryPhaseCertificateWindow) : Prop :=
  0 < w.phaseWindow ∧
    stationaryPhaseCertificateControlled w ∧
      w.certificateBudget ≤ w.phaseWindow + w.oscillationWindow + w.slack

/-- Total size of a stationary phase certificate. -/
def stationaryPhaseCertificate
    (w : StationaryPhaseCertificateWindow) : ℕ :=
  w.phaseWindow + w.oscillationWindow + w.phaseSlack + w.certificateBudget + w.slack

theorem stationaryPhaseCertificate_budget_le_certificate
    (w : StationaryPhaseCertificateWindow)
    (h : stationaryPhaseCertificateReady w) :
    w.certificateBudget ≤ stationaryPhaseCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold stationaryPhaseCertificate
  omega

def sampleStationaryPhaseCertificateWindow :
    StationaryPhaseCertificateWindow where
  phaseWindow := 7
  oscillationWindow := 8
  phaseSlack := 2
  certificateBudget := 14
  slack := 1

example :
    stationaryPhaseCertificateReady
      sampleStationaryPhaseCertificateWindow := by
  norm_num [stationaryPhaseCertificateReady,
    stationaryPhaseCertificateControlled,
    sampleStationaryPhaseCertificateWindow]

example :
    sampleStationaryPhaseCertificateWindow.certificateBudget ≤
      stationaryPhaseCertificate sampleStationaryPhaseCertificateWindow := by
  apply stationaryPhaseCertificate_budget_le_certificate
  norm_num [stationaryPhaseCertificateReady,
    stationaryPhaseCertificateControlled, sampleStationaryPhaseCertificateWindow]

structure StationaryPhaseRefinementCertificate where
  phaseWindow : ℕ
  oscillationWindow : ℕ
  phaseSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StationaryPhaseRefinementCertificate.oscillationControlled
    (c : StationaryPhaseRefinementCertificate) : Prop :=
  c.oscillationWindow ≤ c.phaseWindow + c.phaseSlackWindow + c.slack

def StationaryPhaseRefinementCertificate.certificateBudgetControlled
    (c : StationaryPhaseRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.phaseWindow + c.oscillationWindow + c.phaseSlackWindow + c.slack

def stationaryPhaseRefinementReady
    (c : StationaryPhaseRefinementCertificate) : Prop :=
  0 < c.phaseWindow ∧ c.oscillationControlled ∧ c.certificateBudgetControlled

def StationaryPhaseRefinementCertificate.size
    (c : StationaryPhaseRefinementCertificate) : ℕ :=
  c.phaseWindow + c.oscillationWindow + c.phaseSlackWindow + c.slack

theorem stationaryPhase_certificateBudgetWindow_le_size
    {c : StationaryPhaseRefinementCertificate}
    (h : stationaryPhaseRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleStationaryPhaseRefinementCertificate :
    StationaryPhaseRefinementCertificate :=
  { phaseWindow := 7, oscillationWindow := 8, phaseSlackWindow := 2,
    certificateBudgetWindow := 18, slack := 1 }

example : stationaryPhaseRefinementReady
    sampleStationaryPhaseRefinementCertificate := by
  norm_num [stationaryPhaseRefinementReady,
    StationaryPhaseRefinementCertificate.oscillationControlled,
    StationaryPhaseRefinementCertificate.certificateBudgetControlled,
    sampleStationaryPhaseRefinementCertificate]

example :
    sampleStationaryPhaseRefinementCertificate.certificateBudgetWindow ≤
      sampleStationaryPhaseRefinementCertificate.size := by
  norm_num [StationaryPhaseRefinementCertificate.size,
    sampleStationaryPhaseRefinementCertificate]

structure StationaryPhaseBudgetCertificate where
  phaseWindow : ℕ
  oscillationWindow : ℕ
  phaseSlackWindow : ℕ
  phaseBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StationaryPhaseBudgetCertificate.controlled
    (c : StationaryPhaseBudgetCertificate) : Prop :=
  0 < c.phaseWindow ∧
    c.oscillationWindow ≤ c.phaseWindow + c.phaseSlackWindow + c.slack ∧
      c.phaseBudgetWindow ≤
        c.phaseWindow + c.oscillationWindow + c.phaseSlackWindow + c.slack

def StationaryPhaseBudgetCertificate.budgetControlled
    (c : StationaryPhaseBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.phaseWindow + c.oscillationWindow + c.phaseSlackWindow +
      c.phaseBudgetWindow + c.slack

def StationaryPhaseBudgetCertificate.Ready
    (c : StationaryPhaseBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StationaryPhaseBudgetCertificate.size
    (c : StationaryPhaseBudgetCertificate) : ℕ :=
  c.phaseWindow + c.oscillationWindow + c.phaseSlackWindow +
    c.phaseBudgetWindow + c.slack

theorem stationaryPhase_budgetCertificate_le_size
    (c : StationaryPhaseBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleStationaryPhaseBudgetCertificate :
    StationaryPhaseBudgetCertificate :=
  { phaseWindow := 7
    oscillationWindow := 8
    phaseSlackWindow := 2
    phaseBudgetWindow := 18
    certificateBudgetWindow := 36
    slack := 1 }

example : sampleStationaryPhaseBudgetCertificate.Ready := by
  constructor
  · norm_num [StationaryPhaseBudgetCertificate.controlled,
      sampleStationaryPhaseBudgetCertificate]
  · norm_num [StationaryPhaseBudgetCertificate.budgetControlled,
      sampleStationaryPhaseBudgetCertificate]

example :
    sampleStationaryPhaseBudgetCertificate.certificateBudgetWindow ≤
      sampleStationaryPhaseBudgetCertificate.size := by
  apply stationaryPhase_budgetCertificate_le_size
  constructor
  · norm_num [StationaryPhaseBudgetCertificate.controlled,
      sampleStationaryPhaseBudgetCertificate]
  · norm_num [StationaryPhaseBudgetCertificate.budgetControlled,
      sampleStationaryPhaseBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleStationaryPhaseBudgetCertificate.Ready := by
  constructor
  · norm_num [StationaryPhaseBudgetCertificate.controlled,
      sampleStationaryPhaseBudgetCertificate]
  · norm_num [StationaryPhaseBudgetCertificate.budgetControlled,
      sampleStationaryPhaseBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleStationaryPhaseBudgetCertificate.certificateBudgetWindow ≤
      sampleStationaryPhaseBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List StationaryPhaseBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleStationaryPhaseBudgetCertificate] =
      true := by
  unfold budgetCertificateListReady sampleStationaryPhaseBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.UniformStationaryPhaseWindows
