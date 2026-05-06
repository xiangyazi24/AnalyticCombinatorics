import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Composite scale schema bookkeeping.

Composite scales track inner and outer scales plus a coupling error budget.
-/

namespace AnalyticCombinatorics.Asymptotics.CompositeScaleSchemas

structure CompositeScaleData where
  innerScale : ℕ
  outerScale : ℕ
  couplingError : ℕ
deriving DecidableEq, Repr

def positiveScales (d : CompositeScaleData) : Prop :=
  0 < d.innerScale ∧ 0 < d.outerScale

def couplingControlled (d : CompositeScaleData) : Prop :=
  d.couplingError ≤ d.innerScale + d.outerScale

def compositeScaleReady (d : CompositeScaleData) : Prop :=
  positiveScales d ∧ couplingControlled d

def compositeBudget (d : CompositeScaleData) : ℕ :=
  d.innerScale + d.outerScale + d.couplingError

theorem compositeScaleReady.scales {d : CompositeScaleData}
    (h : compositeScaleReady d) :
    positiveScales d ∧ couplingControlled d ∧ d.couplingError ≤ compositeBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold compositeBudget
  omega

theorem innerScale_le_compositeBudget (d : CompositeScaleData) :
    d.innerScale ≤ compositeBudget d := by
  unfold compositeBudget
  omega

def sampleCompositeScale : CompositeScaleData :=
  { innerScale := 3, outerScale := 8, couplingError := 4 }

example : compositeScaleReady sampleCompositeScale := by
  norm_num [compositeScaleReady, positiveScales, couplingControlled, sampleCompositeScale]

example : compositeBudget sampleCompositeScale = 15 := by
  native_decide

/-- Finite executable readiness audit for composite scale data. -/
def compositeScaleDataListReady
    (data : List CompositeScaleData) : Bool :=
  data.all fun d =>
    0 < d.innerScale &&
      0 < d.outerScale &&
        d.couplingError ≤ d.innerScale + d.outerScale

theorem compositeScaleDataList_readyWindow :
    compositeScaleDataListReady
      [{ innerScale := 2, outerScale := 5, couplingError := 3 },
       { innerScale := 3, outerScale := 8, couplingError := 4 }] = true := by
  unfold compositeScaleDataListReady
  native_decide

structure CompositeScaleWindow where
  innerScale : ℕ
  outerScale : ℕ
  couplingError : ℕ
  compositeMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompositeScaleWindow.scalesReady (w : CompositeScaleWindow) : Prop :=
  0 < w.innerScale ∧ 0 < w.outerScale

def CompositeScaleWindow.couplingControlled (w : CompositeScaleWindow) : Prop :=
  w.couplingError ≤ w.innerScale + w.outerScale + w.slack

def CompositeScaleWindow.massControlled (w : CompositeScaleWindow) : Prop :=
  w.compositeMass ≤ w.innerScale * w.outerScale + w.slack

def CompositeScaleWindow.ready (w : CompositeScaleWindow) : Prop :=
  w.scalesReady ∧ w.couplingControlled ∧ w.massControlled

def CompositeScaleWindow.certificate (w : CompositeScaleWindow) : ℕ :=
  w.innerScale + w.outerScale + w.couplingError + w.compositeMass + w.slack

theorem compositeMass_le_certificate (w : CompositeScaleWindow) :
    w.compositeMass ≤ w.certificate := by
  unfold CompositeScaleWindow.certificate
  omega

def sampleCompositeScaleWindow : CompositeScaleWindow :=
  { innerScale := 3, outerScale := 8, couplingError := 4, compositeMass := 20, slack := 0 }

example : sampleCompositeScaleWindow.ready := by
  norm_num [sampleCompositeScaleWindow, CompositeScaleWindow.ready,
    CompositeScaleWindow.scalesReady, CompositeScaleWindow.couplingControlled,
    CompositeScaleWindow.massControlled]

/-- A refinement certificate for composite scale windows. -/
structure CompositeScaleCertificate where
  innerWindow : ℕ
  outerWindow : ℕ
  couplingWindow : ℕ
  compositeMassWindow : ℕ
  slack : ℕ

/-- Composite scale certificates keep scales positive and control coupling. -/
def compositeScaleCertificateControlled
    (w : CompositeScaleCertificate) : Prop :=
  0 < w.innerWindow ∧
    0 < w.outerWindow ∧
      w.couplingWindow ≤ w.innerWindow + w.outerWindow + w.slack ∧
        w.compositeMassWindow ≤ w.innerWindow * w.outerWindow + w.slack

/-- Readiness for a composite scale certificate. -/
def compositeScaleCertificateReady
    (w : CompositeScaleCertificate) : Prop :=
  compositeScaleCertificateControlled w ∧
    w.compositeMassWindow ≤
      w.innerWindow + w.outerWindow + w.couplingWindow +
        w.compositeMassWindow + w.slack

/-- Total size of a composite scale certificate. -/
def compositeScaleCertificateSize
    (w : CompositeScaleCertificate) : ℕ :=
  w.innerWindow + w.outerWindow + w.couplingWindow +
    w.compositeMassWindow + w.slack

theorem compositeScaleCertificate_mass_le_size
    (w : CompositeScaleCertificate)
    (h : compositeScaleCertificateReady w) :
    w.compositeMassWindow ≤ compositeScaleCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold compositeScaleCertificateSize
  omega

def sampleCompositeScaleCertificate : CompositeScaleCertificate where
  innerWindow := 3
  outerWindow := 8
  couplingWindow := 4
  compositeMassWindow := 20
  slack := 0

example :
    compositeScaleCertificateReady sampleCompositeScaleCertificate := by
  norm_num [compositeScaleCertificateReady,
    compositeScaleCertificateControlled, sampleCompositeScaleCertificate]

example :
    sampleCompositeScaleCertificate.compositeMassWindow ≤
      compositeScaleCertificateSize sampleCompositeScaleCertificate := by
  apply compositeScaleCertificate_mass_le_size
  norm_num [compositeScaleCertificateReady,
    compositeScaleCertificateControlled, sampleCompositeScaleCertificate]

/-- A refinement certificate with the composite-scale budget separated from size. -/
structure CompositeScaleRefinementCertificate where
  innerWindow : ℕ
  outerWindow : ℕ
  couplingWindow : ℕ
  compositeMassWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompositeScaleRefinementCertificate.compositeControlled
    (cert : CompositeScaleRefinementCertificate) : Prop :=
  0 < cert.innerWindow ∧
    0 < cert.outerWindow ∧
      cert.couplingWindow ≤ cert.innerWindow + cert.outerWindow + cert.slack ∧
        cert.compositeMassWindow ≤ cert.innerWindow * cert.outerWindow + cert.slack

def CompositeScaleRefinementCertificate.budgetControlled
    (cert : CompositeScaleRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.innerWindow + cert.outerWindow + cert.couplingWindow +
      cert.compositeMassWindow + cert.slack

def compositeScaleRefinementReady
    (cert : CompositeScaleRefinementCertificate) : Prop :=
  cert.compositeControlled ∧ cert.budgetControlled

def CompositeScaleRefinementCertificate.size
    (cert : CompositeScaleRefinementCertificate) : ℕ :=
  cert.innerWindow + cert.outerWindow + cert.couplingWindow +
    cert.compositeMassWindow + cert.slack

theorem compositeScale_certificateBudgetWindow_le_size
    (cert : CompositeScaleRefinementCertificate)
    (h : compositeScaleRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCompositeScaleRefinementCertificate :
    CompositeScaleRefinementCertificate :=
  { innerWindow := 3, outerWindow := 8, couplingWindow := 4,
    compositeMassWindow := 20, certificateBudgetWindow := 35, slack := 0 }

example :
    compositeScaleRefinementReady sampleCompositeScaleRefinementCertificate := by
  norm_num [compositeScaleRefinementReady,
    CompositeScaleRefinementCertificate.compositeControlled,
    CompositeScaleRefinementCertificate.budgetControlled,
    sampleCompositeScaleRefinementCertificate]

example :
    sampleCompositeScaleRefinementCertificate.certificateBudgetWindow ≤
      sampleCompositeScaleRefinementCertificate.size := by
  apply compositeScale_certificateBudgetWindow_le_size
  norm_num [compositeScaleRefinementReady,
    CompositeScaleRefinementCertificate.compositeControlled,
    CompositeScaleRefinementCertificate.budgetControlled,
    sampleCompositeScaleRefinementCertificate]


structure CompositeScaleSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompositeScaleSchemasBudgetCertificate.controlled
    (c : CompositeScaleSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def CompositeScaleSchemasBudgetCertificate.budgetControlled
    (c : CompositeScaleSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CompositeScaleSchemasBudgetCertificate.Ready
    (c : CompositeScaleSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CompositeScaleSchemasBudgetCertificate.size
    (c : CompositeScaleSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem compositeScaleSchemas_budgetCertificate_le_size
    (c : CompositeScaleSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCompositeScaleSchemasBudgetCertificate :
    CompositeScaleSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleCompositeScaleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CompositeScaleSchemasBudgetCertificate.controlled,
      sampleCompositeScaleSchemasBudgetCertificate]
  · norm_num [CompositeScaleSchemasBudgetCertificate.budgetControlled,
      sampleCompositeScaleSchemasBudgetCertificate]

example :
    sampleCompositeScaleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCompositeScaleSchemasBudgetCertificate.size := by
  apply compositeScaleSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CompositeScaleSchemasBudgetCertificate.controlled,
      sampleCompositeScaleSchemasBudgetCertificate]
  · norm_num [CompositeScaleSchemasBudgetCertificate.budgetControlled,
      sampleCompositeScaleSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCompositeScaleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CompositeScaleSchemasBudgetCertificate.controlled,
      sampleCompositeScaleSchemasBudgetCertificate]
  · norm_num [CompositeScaleSchemasBudgetCertificate.budgetControlled,
      sampleCompositeScaleSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCompositeScaleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCompositeScaleSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CompositeScaleSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCompositeScaleSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCompositeScaleSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.CompositeScaleSchemas
