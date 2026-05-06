import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Stationary-phase schema bookkeeping.

This module records finite nondegeneracy and localization hypotheses for
stationary-phase estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.StationaryPhaseSchemas

structure StationaryPhaseData where
  criticalCount : ℕ
  hessianBudget : ℕ
  localizationRadius : ℕ
deriving DecidableEq, Repr

def hasCriticalPoint (d : StationaryPhaseData) : Prop :=
  0 < d.criticalCount

def nondegenerateHessian (d : StationaryPhaseData) : Prop :=
  0 < d.hessianBudget

def stationaryPhaseReady (d : StationaryPhaseData) : Prop :=
  hasCriticalPoint d ∧ nondegenerateHessian d ∧ 0 < d.localizationRadius

def phaseBudget (d : StationaryPhaseData) : ℕ :=
  d.criticalCount * d.hessianBudget + d.localizationRadius

theorem stationaryPhaseReady.hessian {d : StationaryPhaseData}
    (h : stationaryPhaseReady d) :
    nondegenerateHessian d := h.2.1

theorem phaseBudget_ge_radius (d : StationaryPhaseData) :
    d.localizationRadius ≤ phaseBudget d := by
  unfold phaseBudget
  omega

def sampleStationaryPhase : StationaryPhaseData :=
  { criticalCount := 1, hessianBudget := 6, localizationRadius := 2 }

example : stationaryPhaseReady sampleStationaryPhase := by
  norm_num
    [stationaryPhaseReady, hasCriticalPoint, nondegenerateHessian, sampleStationaryPhase]

example : phaseBudget sampleStationaryPhase = 8 := by
  native_decide

/-- Finite executable readiness audit for stationary phase data. -/
def stationaryPhaseDataListReady
    (data : List StationaryPhaseData) : Bool :=
  data.all fun d =>
    0 < d.criticalCount && 0 < d.hessianBudget && 0 < d.localizationRadius

theorem stationaryPhaseDataList_readyWindow :
    stationaryPhaseDataListReady
      [{ criticalCount := 1, hessianBudget := 3, localizationRadius := 1 },
       { criticalCount := 1, hessianBudget := 6, localizationRadius := 2 }] =
      true := by
  unfold stationaryPhaseDataListReady
  native_decide

structure StationaryPhaseWindow where
  criticalCount : ℕ
  hessianBudget : ℕ
  localizationRadius : ℕ
  oscillationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StationaryPhaseWindow.nonDegenerate (w : StationaryPhaseWindow) : Prop :=
  0 < w.criticalCount ∧ 0 < w.hessianBudget ∧ 0 < w.localizationRadius

def StationaryPhaseWindow.oscillationControlled (w : StationaryPhaseWindow) : Prop :=
  w.oscillationBudget ≤ w.criticalCount * w.hessianBudget + w.localizationRadius + w.slack

def StationaryPhaseWindow.ready (w : StationaryPhaseWindow) : Prop :=
  w.nonDegenerate ∧ w.oscillationControlled

def StationaryPhaseWindow.certificate (w : StationaryPhaseWindow) : ℕ :=
  w.criticalCount + w.hessianBudget + w.localizationRadius + w.oscillationBudget + w.slack

theorem oscillationBudget_le_certificate (w : StationaryPhaseWindow) :
    w.oscillationBudget ≤ w.certificate := by
  unfold StationaryPhaseWindow.certificate
  omega

def sampleStationaryPhaseWindow : StationaryPhaseWindow :=
  { criticalCount := 1, hessianBudget := 6, localizationRadius := 2,
    oscillationBudget := 8, slack := 0 }

example : sampleStationaryPhaseWindow.ready := by
  norm_num [sampleStationaryPhaseWindow, StationaryPhaseWindow.ready,
    StationaryPhaseWindow.nonDegenerate, StationaryPhaseWindow.oscillationControlled]

/-- A refinement certificate for stationary-phase windows. -/
structure StationaryPhaseCertificate where
  criticalWindow : ℕ
  hessianWindow : ℕ
  localizationWindow : ℕ
  oscillationWindow : ℕ
  slack : ℕ

/-- Nondegenerate stationary-phase data controls the oscillation budget. -/
def stationaryPhaseCertificateControlled
    (w : StationaryPhaseCertificate) : Prop :=
  0 < w.criticalWindow ∧
    0 < w.hessianWindow ∧
      0 < w.localizationWindow ∧
        w.oscillationWindow ≤
          w.criticalWindow * w.hessianWindow + w.localizationWindow + w.slack

/-- Readiness for a stationary-phase certificate. -/
def stationaryPhaseCertificateReady
    (w : StationaryPhaseCertificate) : Prop :=
  stationaryPhaseCertificateControlled w ∧
    w.oscillationWindow ≤
      w.criticalWindow + w.hessianWindow + w.localizationWindow + w.oscillationWindow + w.slack

/-- Total size of a stationary-phase certificate. -/
def stationaryPhaseCertificateSize
    (w : StationaryPhaseCertificate) : ℕ :=
  w.criticalWindow + w.hessianWindow + w.localizationWindow + w.oscillationWindow + w.slack

theorem stationaryPhaseCertificate_oscillation_le_size
    (w : StationaryPhaseCertificate)
    (h : stationaryPhaseCertificateReady w) :
    w.oscillationWindow ≤ stationaryPhaseCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold stationaryPhaseCertificateSize
  omega

def sampleStationaryPhaseCertificate : StationaryPhaseCertificate where
  criticalWindow := 1
  hessianWindow := 6
  localizationWindow := 2
  oscillationWindow := 8
  slack := 0

example :
    stationaryPhaseCertificateReady sampleStationaryPhaseCertificate := by
  norm_num [stationaryPhaseCertificateReady,
    stationaryPhaseCertificateControlled, sampleStationaryPhaseCertificate]

example :
    sampleStationaryPhaseCertificate.oscillationWindow ≤
      stationaryPhaseCertificateSize sampleStationaryPhaseCertificate := by
  apply stationaryPhaseCertificate_oscillation_le_size
  norm_num [stationaryPhaseCertificateReady,
    stationaryPhaseCertificateControlled, sampleStationaryPhaseCertificate]

/-- A refinement certificate with the stationary-phase budget separated from size. -/
structure StationaryPhaseRefinementCertificate where
  criticalWindow : ℕ
  hessianWindow : ℕ
  localizationWindow : ℕ
  oscillationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StationaryPhaseRefinementCertificate.phaseControlled
    (cert : StationaryPhaseRefinementCertificate) : Prop :=
  0 < cert.criticalWindow ∧
    0 < cert.hessianWindow ∧
      0 < cert.localizationWindow ∧
        cert.oscillationWindow ≤
          cert.criticalWindow * cert.hessianWindow + cert.localizationWindow + cert.slack

def StationaryPhaseRefinementCertificate.budgetControlled
    (cert : StationaryPhaseRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.criticalWindow + cert.hessianWindow + cert.localizationWindow +
      cert.oscillationWindow + cert.slack

def stationaryPhaseRefinementReady
    (cert : StationaryPhaseRefinementCertificate) : Prop :=
  cert.phaseControlled ∧ cert.budgetControlled

def StationaryPhaseRefinementCertificate.size
    (cert : StationaryPhaseRefinementCertificate) : ℕ :=
  cert.criticalWindow + cert.hessianWindow + cert.localizationWindow +
    cert.oscillationWindow + cert.slack

theorem stationaryPhase_certificateBudgetWindow_le_size
    (cert : StationaryPhaseRefinementCertificate)
    (h : stationaryPhaseRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleStationaryPhaseRefinementCertificate :
    StationaryPhaseRefinementCertificate :=
  { criticalWindow := 1, hessianWindow := 6, localizationWindow := 2,
    oscillationWindow := 8, certificateBudgetWindow := 17, slack := 0 }

example :
    stationaryPhaseRefinementReady sampleStationaryPhaseRefinementCertificate := by
  norm_num [stationaryPhaseRefinementReady,
    StationaryPhaseRefinementCertificate.phaseControlled,
    StationaryPhaseRefinementCertificate.budgetControlled,
    sampleStationaryPhaseRefinementCertificate]

example :
    sampleStationaryPhaseRefinementCertificate.certificateBudgetWindow ≤
      sampleStationaryPhaseRefinementCertificate.size := by
  apply stationaryPhase_certificateBudgetWindow_le_size
  norm_num [stationaryPhaseRefinementReady,
    StationaryPhaseRefinementCertificate.phaseControlled,
    StationaryPhaseRefinementCertificate.budgetControlled,
    sampleStationaryPhaseRefinementCertificate]


structure StationaryPhaseSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StationaryPhaseSchemasBudgetCertificate.controlled
    (c : StationaryPhaseSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def StationaryPhaseSchemasBudgetCertificate.budgetControlled
    (c : StationaryPhaseSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def StationaryPhaseSchemasBudgetCertificate.Ready
    (c : StationaryPhaseSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StationaryPhaseSchemasBudgetCertificate.size
    (c : StationaryPhaseSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem stationaryPhaseSchemas_budgetCertificate_le_size
    (c : StationaryPhaseSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleStationaryPhaseSchemasBudgetCertificate :
    StationaryPhaseSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleStationaryPhaseSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [StationaryPhaseSchemasBudgetCertificate.controlled,
      sampleStationaryPhaseSchemasBudgetCertificate]
  · norm_num [StationaryPhaseSchemasBudgetCertificate.budgetControlled,
      sampleStationaryPhaseSchemasBudgetCertificate]

example :
    sampleStationaryPhaseSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleStationaryPhaseSchemasBudgetCertificate.size := by
  apply stationaryPhaseSchemas_budgetCertificate_le_size
  constructor
  · norm_num [StationaryPhaseSchemasBudgetCertificate.controlled,
      sampleStationaryPhaseSchemasBudgetCertificate]
  · norm_num [StationaryPhaseSchemasBudgetCertificate.budgetControlled,
      sampleStationaryPhaseSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleStationaryPhaseSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [StationaryPhaseSchemasBudgetCertificate.controlled,
      sampleStationaryPhaseSchemasBudgetCertificate]
  · norm_num [StationaryPhaseSchemasBudgetCertificate.budgetControlled,
      sampleStationaryPhaseSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleStationaryPhaseSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleStationaryPhaseSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List StationaryPhaseSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleStationaryPhaseSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleStationaryPhaseSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.StationaryPhaseSchemas
