import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Asymptotic inversion schema bookkeeping.

The finite data records monotone inverse windows and residual error budgets.
-/

namespace AnalyticCombinatorics.Asymptotics.AsymptoticInversionSchemas

structure InversionDatum where
  inputScale : ℕ
  outputScale : ℕ
  residualBudget : ℕ
deriving DecidableEq, Repr

def scalesPositive (d : InversionDatum) : Prop :=
  0 < d.inputScale ∧ 0 < d.outputScale

def residualControlled (d : InversionDatum) : Prop :=
  d.residualBudget ≤ d.inputScale + d.outputScale

def inversionReady (d : InversionDatum) : Prop :=
  scalesPositive d ∧ residualControlled d

def inversionBudget (d : InversionDatum) : ℕ :=
  d.inputScale + d.outputScale + d.residualBudget

theorem inversionReady.scales {d : InversionDatum}
    (h : inversionReady d) :
    scalesPositive d ∧ residualControlled d ∧ d.residualBudget ≤ inversionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold inversionBudget
  omega

theorem inputScale_le_budget (d : InversionDatum) :
    d.inputScale ≤ inversionBudget d := by
  unfold inversionBudget
  omega

def sampleInversion : InversionDatum :=
  { inputScale := 4, outputScale := 6, residualBudget := 3 }

example : inversionReady sampleInversion := by
  norm_num [inversionReady, scalesPositive, residualControlled, sampleInversion]

example : inversionBudget sampleInversion = 13 := by
  native_decide

/-- Finite executable readiness audit for asymptotic inversion data. -/
def inversionDatumListReady (data : List InversionDatum) : Bool :=
  data.all fun d =>
    0 < d.inputScale &&
      0 < d.outputScale &&
        d.residualBudget ≤ d.inputScale + d.outputScale

theorem inversionDatumList_readyWindow :
    inversionDatumListReady
      [{ inputScale := 3, outputScale := 4, residualBudget := 2 },
       { inputScale := 4, outputScale := 6, residualBudget := 3 }] = true := by
  unfold inversionDatumListReady
  native_decide

structure InversionWindow where
  inputScale : ℕ
  outputScale : ℕ
  inverseError : ℕ
  monotonicityBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def InversionWindow.scalesReady (w : InversionWindow) : Prop :=
  0 < w.inputScale ∧ 0 < w.outputScale

def InversionWindow.errorControlled (w : InversionWindow) : Prop :=
  w.inverseError ≤ w.inputScale + w.outputScale + w.slack

def InversionWindow.monotoneControlled (w : InversionWindow) : Prop :=
  w.monotonicityBudget ≤ w.inputScale + w.outputScale + w.slack

def InversionWindow.ready (w : InversionWindow) : Prop :=
  w.scalesReady ∧ w.errorControlled ∧ w.monotoneControlled

def InversionWindow.certificate (w : InversionWindow) : ℕ :=
  w.inputScale + w.outputScale + w.inverseError + w.monotonicityBudget + w.slack

theorem inverseError_le_certificate (w : InversionWindow) :
    w.inverseError ≤ w.certificate := by
  unfold InversionWindow.certificate
  omega

def sampleInversionWindow : InversionWindow :=
  { inputScale := 4, outputScale := 6, inverseError := 3, monotonicityBudget := 5, slack := 0 }

example : sampleInversionWindow.ready := by
  norm_num [sampleInversionWindow, InversionWindow.ready, InversionWindow.scalesReady,
    InversionWindow.errorControlled, InversionWindow.monotoneControlled]

/-- A refinement certificate for asymptotic inversion windows. -/
structure InversionCertificate where
  inputWindow : ℕ
  outputWindow : ℕ
  inverseErrorWindow : ℕ
  monotonicityWindow : ℕ
  slack : ℕ

/-- Scales are positive and inversion errors are controlled. -/
def inversionCertificateControlled
    (w : InversionCertificate) : Prop :=
  0 < w.inputWindow ∧
    0 < w.outputWindow ∧
      w.inverseErrorWindow ≤ w.inputWindow + w.outputWindow + w.slack ∧
        w.monotonicityWindow ≤ w.inputWindow + w.outputWindow + w.slack

/-- Readiness for an inversion certificate. -/
def inversionCertificateReady
    (w : InversionCertificate) : Prop :=
  inversionCertificateControlled w ∧
    w.inverseErrorWindow ≤
      w.inputWindow + w.outputWindow + w.inverseErrorWindow +
        w.monotonicityWindow + w.slack

/-- Total size of an inversion certificate. -/
def inversionCertificateSize (w : InversionCertificate) : ℕ :=
  w.inputWindow + w.outputWindow + w.inverseErrorWindow +
    w.monotonicityWindow + w.slack

theorem inversionCertificate_error_le_size
    (w : InversionCertificate)
    (h : inversionCertificateReady w) :
    w.inverseErrorWindow ≤ inversionCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold inversionCertificateSize
  omega

def sampleInversionCertificate : InversionCertificate where
  inputWindow := 4
  outputWindow := 6
  inverseErrorWindow := 3
  monotonicityWindow := 5
  slack := 0

example :
    inversionCertificateReady sampleInversionCertificate := by
  norm_num [inversionCertificateReady,
    inversionCertificateControlled, sampleInversionCertificate]

example :
    sampleInversionCertificate.inverseErrorWindow ≤
      inversionCertificateSize sampleInversionCertificate := by
  apply inversionCertificate_error_le_size
  norm_num [inversionCertificateReady,
    inversionCertificateControlled, sampleInversionCertificate]

/-- A refinement certificate with the inversion budget separated from size. -/
structure InversionRefinementCertificate where
  inputWindow : ℕ
  outputWindow : ℕ
  inverseErrorWindow : ℕ
  monotonicityWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def InversionRefinementCertificate.inversionControlled
    (cert : InversionRefinementCertificate) : Prop :=
  0 < cert.inputWindow ∧
    0 < cert.outputWindow ∧
      cert.inverseErrorWindow ≤ cert.inputWindow + cert.outputWindow + cert.slack ∧
        cert.monotonicityWindow ≤ cert.inputWindow + cert.outputWindow + cert.slack

def InversionRefinementCertificate.budgetControlled
    (cert : InversionRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.inputWindow + cert.outputWindow + cert.inverseErrorWindow +
      cert.monotonicityWindow + cert.slack

def inversionRefinementReady
    (cert : InversionRefinementCertificate) : Prop :=
  cert.inversionControlled ∧ cert.budgetControlled

def InversionRefinementCertificate.size
    (cert : InversionRefinementCertificate) : ℕ :=
  cert.inputWindow + cert.outputWindow + cert.inverseErrorWindow +
    cert.monotonicityWindow + cert.slack

theorem inversion_certificateBudgetWindow_le_size
    (cert : InversionRefinementCertificate)
    (h : inversionRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleInversionRefinementCertificate : InversionRefinementCertificate :=
  { inputWindow := 4, outputWindow := 6, inverseErrorWindow := 3,
    monotonicityWindow := 5, certificateBudgetWindow := 18, slack := 0 }

example : inversionRefinementReady sampleInversionRefinementCertificate := by
  norm_num [inversionRefinementReady,
    InversionRefinementCertificate.inversionControlled,
    InversionRefinementCertificate.budgetControlled,
    sampleInversionRefinementCertificate]

example :
    sampleInversionRefinementCertificate.certificateBudgetWindow ≤
      sampleInversionRefinementCertificate.size := by
  apply inversion_certificateBudgetWindow_le_size
  norm_num [inversionRefinementReady,
    InversionRefinementCertificate.inversionControlled,
    InversionRefinementCertificate.budgetControlled,
    sampleInversionRefinementCertificate]


structure AsymptoticInversionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AsymptoticInversionSchemasBudgetCertificate.controlled
    (c : AsymptoticInversionSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def AsymptoticInversionSchemasBudgetCertificate.budgetControlled
    (c : AsymptoticInversionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AsymptoticInversionSchemasBudgetCertificate.Ready
    (c : AsymptoticInversionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AsymptoticInversionSchemasBudgetCertificate.size
    (c : AsymptoticInversionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem asymptoticInversionSchemas_budgetCertificate_le_size
    (c : AsymptoticInversionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAsymptoticInversionSchemasBudgetCertificate :
    AsymptoticInversionSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleAsymptoticInversionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticInversionSchemasBudgetCertificate.controlled,
      sampleAsymptoticInversionSchemasBudgetCertificate]
  · norm_num [AsymptoticInversionSchemasBudgetCertificate.budgetControlled,
      sampleAsymptoticInversionSchemasBudgetCertificate]

example :
    sampleAsymptoticInversionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticInversionSchemasBudgetCertificate.size := by
  apply asymptoticInversionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [AsymptoticInversionSchemasBudgetCertificate.controlled,
      sampleAsymptoticInversionSchemasBudgetCertificate]
  · norm_num [AsymptoticInversionSchemasBudgetCertificate.budgetControlled,
      sampleAsymptoticInversionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAsymptoticInversionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticInversionSchemasBudgetCertificate.controlled,
      sampleAsymptoticInversionSchemasBudgetCertificate]
  · norm_num [AsymptoticInversionSchemasBudgetCertificate.budgetControlled,
      sampleAsymptoticInversionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAsymptoticInversionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticInversionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AsymptoticInversionSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAsymptoticInversionSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAsymptoticInversionSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.AsymptoticInversionSchemas
