import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Discrete logarithmic-scale schemas.

The module models scale hierarchies by iterated integer budgets, avoiding
any dependence on analytic logarithm APIs.
-/

namespace AnalyticCombinatorics.Asymptotics.LogarithmicScaleSchemas

def scaleLevel (base n : ℕ) : ℕ :=
  base ^ (n + 1)

def scaleSeparated (base : ℕ) : Prop :=
  1 < base

def scaleBudget (base depth : ℕ) : ℕ :=
  (List.range (depth + 1)).map (scaleLevel base) |>.sum

theorem scaleLevel_positive {base n : ℕ}
    (h : 0 < base) :
    0 < scaleLevel base n := by
  unfold scaleLevel
  exact pow_pos h (n + 1)

theorem scaleSeparated.positive {base : ℕ}
    (h : scaleSeparated base) :
    0 < base := by
  unfold scaleSeparated at h
  omega

example : scaleLevel 2 4 = 32 := by
  native_decide

example : scaleBudget 2 2 = 14 := by
  native_decide

example : scaleSeparated 3 := by
  norm_num [scaleSeparated]

structure LogarithmicScaleWindow where
  base : ℕ
  depth : ℕ
  terminalScale : ℕ
  accumulatedBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogarithmicScaleWindow.baseReady (w : LogarithmicScaleWindow) : Prop :=
  1 < w.base

def LogarithmicScaleWindow.terminalControlled (w : LogarithmicScaleWindow) : Prop :=
  w.terminalScale ≤ scaleLevel w.base w.depth + w.slack

def LogarithmicScaleWindow.budgetControlled (w : LogarithmicScaleWindow) : Prop :=
  w.terminalScale ≤ w.accumulatedBudget + w.slack

def LogarithmicScaleWindow.ready (w : LogarithmicScaleWindow) : Prop :=
  w.baseReady ∧ w.terminalControlled ∧ w.budgetControlled

def LogarithmicScaleWindow.certificate (w : LogarithmicScaleWindow) : ℕ :=
  w.base + w.depth + w.terminalScale + w.accumulatedBudget + w.slack

theorem terminalScale_le_certificate (w : LogarithmicScaleWindow) :
    w.terminalScale ≤ w.certificate := by
  unfold LogarithmicScaleWindow.certificate
  omega

def sampleLogarithmicScaleWindow : LogarithmicScaleWindow :=
  { base := 2, depth := 3, terminalScale := 16, accumulatedBudget := 30, slack := 0 }

example : sampleLogarithmicScaleWindow.ready := by
  norm_num [sampleLogarithmicScaleWindow, LogarithmicScaleWindow.ready,
    LogarithmicScaleWindow.baseReady, LogarithmicScaleWindow.terminalControlled,
    LogarithmicScaleWindow.budgetControlled, scaleLevel]

/-- Finite executable readiness audit for logarithmic scale windows. -/
def logarithmicScaleWindowListReady
    (windows : List LogarithmicScaleWindow) : Bool :=
  windows.all fun w =>
    1 < w.base &&
      w.terminalScale ≤ scaleLevel w.base w.depth + w.slack &&
        w.terminalScale ≤ w.accumulatedBudget + w.slack

theorem logarithmicScaleWindowList_readyWindow :
    logarithmicScaleWindowListReady
      [{ base := 2, depth := 2, terminalScale := 8,
         accumulatedBudget := 14, slack := 0 },
       { base := 2, depth := 3, terminalScale := 16,
         accumulatedBudget := 30, slack := 0 }] = true := by
  unfold logarithmicScaleWindowListReady
  native_decide

/-- A refinement certificate for logarithmic scale windows. -/
structure LogarithmicScaleCertificate where
  baseWindow : ℕ
  depthWindow : ℕ
  terminalWindow : ℕ
  accumulatedWindow : ℕ
  slack : ℕ

/-- Terminal scale and accumulated budget are controlled by the base and depth. -/
def logarithmicScaleCertificateControlled
    (w : LogarithmicScaleCertificate) : Prop :=
  1 < w.baseWindow ∧
    w.terminalWindow ≤ scaleLevel w.baseWindow w.depthWindow + w.slack ∧
      w.terminalWindow ≤ w.accumulatedWindow + w.slack

/-- Readiness for a logarithmic scale certificate. -/
def logarithmicScaleCertificateReady
    (w : LogarithmicScaleCertificate) : Prop :=
  logarithmicScaleCertificateControlled w ∧
    w.accumulatedWindow ≤
      w.baseWindow + w.depthWindow + w.terminalWindow + w.accumulatedWindow + w.slack

/-- Total size of a logarithmic scale certificate. -/
def logarithmicScaleCertificateSize
    (w : LogarithmicScaleCertificate) : ℕ :=
  w.baseWindow + w.depthWindow + w.terminalWindow + w.accumulatedWindow + w.slack

theorem logarithmicScaleCertificate_accumulated_le_size
    (w : LogarithmicScaleCertificate)
    (h : logarithmicScaleCertificateReady w) :
    w.accumulatedWindow ≤ logarithmicScaleCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold logarithmicScaleCertificateSize
  omega

def sampleLogarithmicScaleCertificate : LogarithmicScaleCertificate where
  baseWindow := 2
  depthWindow := 3
  terminalWindow := 16
  accumulatedWindow := 30
  slack := 0

example :
    logarithmicScaleCertificateReady sampleLogarithmicScaleCertificate := by
  norm_num [logarithmicScaleCertificateReady,
    logarithmicScaleCertificateControlled, sampleLogarithmicScaleCertificate,
    scaleLevel]

example :
    sampleLogarithmicScaleCertificate.accumulatedWindow ≤
      logarithmicScaleCertificateSize sampleLogarithmicScaleCertificate := by
  apply logarithmicScaleCertificate_accumulated_le_size
  norm_num [logarithmicScaleCertificateReady,
    logarithmicScaleCertificateControlled, sampleLogarithmicScaleCertificate,
    scaleLevel]

/-- A refinement certificate with the accumulated-scale budget separated from size. -/
structure LogarithmicScaleRefinementCertificate where
  baseWindow : ℕ
  depthWindow : ℕ
  terminalWindow : ℕ
  accumulatedWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def LogarithmicScaleRefinementCertificate.scaleControlled
    (cert : LogarithmicScaleRefinementCertificate) : Prop :=
  1 < cert.baseWindow ∧
    cert.terminalWindow ≤ scaleLevel cert.baseWindow cert.depthWindow + cert.slack ∧
      cert.terminalWindow ≤ cert.accumulatedWindow + cert.slack

def LogarithmicScaleRefinementCertificate.budgetControlled
    (cert : LogarithmicScaleRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.baseWindow + cert.depthWindow + cert.terminalWindow +
      cert.accumulatedWindow + cert.slack

def logarithmicScaleRefinementReady
    (cert : LogarithmicScaleRefinementCertificate) : Prop :=
  cert.scaleControlled ∧ cert.budgetControlled

def LogarithmicScaleRefinementCertificate.size
    (cert : LogarithmicScaleRefinementCertificate) : ℕ :=
  cert.baseWindow + cert.depthWindow + cert.terminalWindow +
    cert.accumulatedWindow + cert.slack

theorem logarithmicScale_certificateBudgetWindow_le_size
    (cert : LogarithmicScaleRefinementCertificate)
    (h : logarithmicScaleRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLogarithmicScaleRefinementCertificate :
    LogarithmicScaleRefinementCertificate where
  baseWindow := 2
  depthWindow := 3
  terminalWindow := 16
  accumulatedWindow := 30
  certificateBudgetWindow := 51
  slack := 0

example :
    logarithmicScaleRefinementReady sampleLogarithmicScaleRefinementCertificate := by
  norm_num [logarithmicScaleRefinementReady,
    LogarithmicScaleRefinementCertificate.scaleControlled,
    LogarithmicScaleRefinementCertificate.budgetControlled,
    sampleLogarithmicScaleRefinementCertificate, scaleLevel]

example :
    sampleLogarithmicScaleRefinementCertificate.certificateBudgetWindow ≤
      sampleLogarithmicScaleRefinementCertificate.size := by
  apply logarithmicScale_certificateBudgetWindow_le_size
  norm_num [logarithmicScaleRefinementReady,
    LogarithmicScaleRefinementCertificate.scaleControlled,
    LogarithmicScaleRefinementCertificate.budgetControlled,
    sampleLogarithmicScaleRefinementCertificate, scaleLevel]


structure LogarithmicScaleSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogarithmicScaleSchemasBudgetCertificate.controlled
    (c : LogarithmicScaleSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def LogarithmicScaleSchemasBudgetCertificate.budgetControlled
    (c : LogarithmicScaleSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LogarithmicScaleSchemasBudgetCertificate.Ready
    (c : LogarithmicScaleSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LogarithmicScaleSchemasBudgetCertificate.size
    (c : LogarithmicScaleSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem logarithmicScaleSchemas_budgetCertificate_le_size
    (c : LogarithmicScaleSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLogarithmicScaleSchemasBudgetCertificate :
    LogarithmicScaleSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleLogarithmicScaleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LogarithmicScaleSchemasBudgetCertificate.controlled,
      sampleLogarithmicScaleSchemasBudgetCertificate]
  · norm_num [LogarithmicScaleSchemasBudgetCertificate.budgetControlled,
      sampleLogarithmicScaleSchemasBudgetCertificate]

example :
    sampleLogarithmicScaleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLogarithmicScaleSchemasBudgetCertificate.size := by
  apply logarithmicScaleSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LogarithmicScaleSchemasBudgetCertificate.controlled,
      sampleLogarithmicScaleSchemasBudgetCertificate]
  · norm_num [LogarithmicScaleSchemasBudgetCertificate.budgetControlled,
      sampleLogarithmicScaleSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLogarithmicScaleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LogarithmicScaleSchemasBudgetCertificate.controlled,
      sampleLogarithmicScaleSchemasBudgetCertificate]
  · norm_num [LogarithmicScaleSchemasBudgetCertificate.budgetControlled,
      sampleLogarithmicScaleSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLogarithmicScaleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLogarithmicScaleSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LogarithmicScaleSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLogarithmicScaleSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLogarithmicScaleSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.LogarithmicScaleSchemas
