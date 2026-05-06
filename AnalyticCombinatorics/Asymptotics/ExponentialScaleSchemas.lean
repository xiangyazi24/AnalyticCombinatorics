import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Exponential scale schema bookkeeping.

The finite schema records base, exponent, and remainder budgets for
exponential asymptotic scales.
-/

namespace AnalyticCombinatorics.Asymptotics.ExponentialScaleSchemas

structure ExponentialScaleData where
  base : ℕ
  exponent : ℕ
  remainderBudget : ℕ
deriving DecidableEq, Repr

def baseNontrivial (d : ExponentialScaleData) : Prop :=
  1 < d.base

def exponentPositive (d : ExponentialScaleData) : Prop :=
  0 < d.exponent

def exponentialScaleReady (d : ExponentialScaleData) : Prop :=
  baseNontrivial d ∧ exponentPositive d

def exponentialScale (d : ExponentialScaleData) : ℕ :=
  d.base ^ d.exponent + d.remainderBudget

theorem exponentialScaleReady.base {d : ExponentialScaleData}
    (h : exponentialScaleReady d) :
    baseNontrivial d ∧ exponentPositive d ∧ d.remainderBudget ≤ exponentialScale d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold exponentialScale
  omega

theorem remainder_le_exponentialScale (d : ExponentialScaleData) :
    d.remainderBudget ≤ exponentialScale d := by
  unfold exponentialScale
  omega

def sampleExponentialScale : ExponentialScaleData :=
  { base := 2, exponent := 5, remainderBudget := 3 }

example : exponentialScaleReady sampleExponentialScale := by
  norm_num [exponentialScaleReady, baseNontrivial, exponentPositive, sampleExponentialScale]

example : exponentialScale sampleExponentialScale = 35 := by
  native_decide

/-- Finite executable readiness audit for exponential scale data. -/
def exponentialScaleDataListReady
    (data : List ExponentialScaleData) : Bool :=
  data.all fun d => 1 < d.base && 0 < d.exponent

theorem exponentialScaleDataList_readyWindow :
    exponentialScaleDataListReady
      [{ base := 2, exponent := 3, remainderBudget := 1 },
       { base := 2, exponent := 5, remainderBudget := 3 }] = true := by
  unfold exponentialScaleDataListReady
  native_decide

structure ExponentialScaleWindow where
  base : ℕ
  exponent : ℕ
  remainderBudget : ℕ
  prefactorBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExponentialScaleWindow.remainderControlled (w : ExponentialScaleWindow) : Prop :=
  w.remainderBudget ≤ w.base ^ w.exponent + w.slack

def ExponentialScaleWindow.prefactorControlled (w : ExponentialScaleWindow) : Prop :=
  w.prefactorBudget ≤ w.base ^ w.exponent + w.remainderBudget + w.slack

def exponentialScaleWindowReady (w : ExponentialScaleWindow) : Prop :=
  1 < w.base ∧
    0 < w.exponent ∧
    w.remainderControlled ∧
    w.prefactorControlled

def ExponentialScaleWindow.certificate (w : ExponentialScaleWindow) : ℕ :=
  w.base ^ w.exponent + w.remainderBudget + w.slack

theorem exponentialScale_prefactorBudget_le_certificate {w : ExponentialScaleWindow}
    (h : exponentialScaleWindowReady w) :
    w.prefactorBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hprefactor⟩
  exact hprefactor

def sampleExponentialScaleWindow : ExponentialScaleWindow :=
  { base := 2, exponent := 5, remainderBudget := 3, prefactorBudget := 34, slack := 0 }

example : exponentialScaleWindowReady sampleExponentialScaleWindow := by
  norm_num [exponentialScaleWindowReady, ExponentialScaleWindow.remainderControlled,
    ExponentialScaleWindow.prefactorControlled, sampleExponentialScaleWindow]

example : sampleExponentialScaleWindow.certificate = 35 := by
  native_decide

structure ExponentialScaleCertificate where
  baseWindow : ℕ
  exponentWindow : ℕ
  remainderWindow : ℕ
  prefactorWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExponentialScaleCertificate.remainderControlled
    (c : ExponentialScaleCertificate) : Prop :=
  c.remainderWindow ≤ c.baseWindow ^ c.exponentWindow + c.slack

def ExponentialScaleCertificate.prefactorControlled
    (c : ExponentialScaleCertificate) : Prop :=
  c.prefactorWindow ≤ c.baseWindow ^ c.exponentWindow + c.remainderWindow + c.slack

def exponentialScaleCertificateReady
    (c : ExponentialScaleCertificate) : Prop :=
  1 < c.baseWindow ∧
    0 < c.exponentWindow ∧
    c.remainderControlled ∧
    c.prefactorControlled

def ExponentialScaleCertificate.size
    (c : ExponentialScaleCertificate) : ℕ :=
  c.baseWindow ^ c.exponentWindow + c.remainderWindow + c.slack

theorem exponentialScale_prefactorWindow_le_size
    {c : ExponentialScaleCertificate}
    (h : exponentialScaleCertificateReady c) :
    c.prefactorWindow ≤ c.size := by
  rcases h with ⟨_, _, _, hprefactor⟩
  exact hprefactor

def sampleExponentialScaleCertificate : ExponentialScaleCertificate :=
  { baseWindow := 2, exponentWindow := 5, remainderWindow := 3,
    prefactorWindow := 34, slack := 0 }

example : exponentialScaleCertificateReady sampleExponentialScaleCertificate := by
  norm_num [exponentialScaleCertificateReady,
    ExponentialScaleCertificate.remainderControlled,
    ExponentialScaleCertificate.prefactorControlled,
    sampleExponentialScaleCertificate]

example :
    sampleExponentialScaleCertificate.prefactorWindow ≤
      sampleExponentialScaleCertificate.size := by
  norm_num [ExponentialScaleCertificate.size, sampleExponentialScaleCertificate]

/-- A refinement certificate with the exponential prefactor budget separated from size. -/
structure ExponentialScaleRefinementCertificate where
  baseWindow : ℕ
  exponentWindow : ℕ
  remainderWindow : ℕ
  prefactorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExponentialScaleRefinementCertificate.scaleControlled
    (cert : ExponentialScaleRefinementCertificate) : Prop :=
  1 < cert.baseWindow ∧
    0 < cert.exponentWindow ∧
      cert.remainderWindow ≤ cert.baseWindow ^ cert.exponentWindow + cert.slack ∧
        cert.prefactorWindow ≤
          cert.baseWindow ^ cert.exponentWindow + cert.remainderWindow + cert.slack

def ExponentialScaleRefinementCertificate.budgetControlled
    (cert : ExponentialScaleRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.baseWindow ^ cert.exponentWindow + cert.remainderWindow + cert.slack

def exponentialScaleRefinementReady
    (cert : ExponentialScaleRefinementCertificate) : Prop :=
  cert.scaleControlled ∧ cert.budgetControlled

def ExponentialScaleRefinementCertificate.size
    (cert : ExponentialScaleRefinementCertificate) : ℕ :=
  cert.baseWindow ^ cert.exponentWindow + cert.remainderWindow + cert.slack

theorem exponentialScale_certificateBudgetWindow_le_size
    (cert : ExponentialScaleRefinementCertificate)
    (h : exponentialScaleRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleExponentialScaleRefinementCertificate :
    ExponentialScaleRefinementCertificate :=
  { baseWindow := 2, exponentWindow := 5, remainderWindow := 3,
    prefactorWindow := 34, certificateBudgetWindow := 35, slack := 0 }

example :
    exponentialScaleRefinementReady sampleExponentialScaleRefinementCertificate := by
  norm_num [exponentialScaleRefinementReady,
    ExponentialScaleRefinementCertificate.scaleControlled,
    ExponentialScaleRefinementCertificate.budgetControlled,
    sampleExponentialScaleRefinementCertificate]

example :
    sampleExponentialScaleRefinementCertificate.certificateBudgetWindow ≤
      sampleExponentialScaleRefinementCertificate.size := by
  apply exponentialScale_certificateBudgetWindow_le_size
  norm_num [exponentialScaleRefinementReady,
    ExponentialScaleRefinementCertificate.scaleControlled,
    ExponentialScaleRefinementCertificate.budgetControlled,
    sampleExponentialScaleRefinementCertificate]


structure ExponentialScaleSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExponentialScaleSchemasBudgetCertificate.controlled
    (c : ExponentialScaleSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def ExponentialScaleSchemasBudgetCertificate.budgetControlled
    (c : ExponentialScaleSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ExponentialScaleSchemasBudgetCertificate.Ready
    (c : ExponentialScaleSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ExponentialScaleSchemasBudgetCertificate.size
    (c : ExponentialScaleSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem exponentialScaleSchemas_budgetCertificate_le_size
    (c : ExponentialScaleSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleExponentialScaleSchemasBudgetCertificate :
    ExponentialScaleSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleExponentialScaleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialScaleSchemasBudgetCertificate.controlled,
      sampleExponentialScaleSchemasBudgetCertificate]
  · norm_num [ExponentialScaleSchemasBudgetCertificate.budgetControlled,
      sampleExponentialScaleSchemasBudgetCertificate]

example :
    sampleExponentialScaleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialScaleSchemasBudgetCertificate.size := by
  apply exponentialScaleSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ExponentialScaleSchemasBudgetCertificate.controlled,
      sampleExponentialScaleSchemasBudgetCertificate]
  · norm_num [ExponentialScaleSchemasBudgetCertificate.budgetControlled,
      sampleExponentialScaleSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleExponentialScaleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialScaleSchemasBudgetCertificate.controlled,
      sampleExponentialScaleSchemasBudgetCertificate]
  · norm_num [ExponentialScaleSchemasBudgetCertificate.budgetControlled,
      sampleExponentialScaleSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleExponentialScaleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialScaleSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ExponentialScaleSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleExponentialScaleSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleExponentialScaleSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.ExponentialScaleSchemas
