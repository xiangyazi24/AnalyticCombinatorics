import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Poisson-Charlier correction bookkeeping.

The module records finite correction orders and error budgets used in
depoissonization expansions.
-/

namespace AnalyticCombinatorics.Asymptotics.PoissonCharlierSchemas

structure CharlierCorrection where
  order : ℕ
  coefficientBudget : ℕ
  remainderBudget : ℕ
deriving DecidableEq, Repr

def nonzeroCorrection (c : CharlierCorrection) : Prop :=
  0 < c.order

def correctionControlled (c : CharlierCorrection) : Prop :=
  nonzeroCorrection c ∧ c.remainderBudget ≤ c.coefficientBudget

def totalCorrectionBudget (c : CharlierCorrection) : ℕ :=
  c.coefficientBudget + c.remainderBudget

theorem correctionControlled.order {c : CharlierCorrection}
    (h : correctionControlled c) :
    nonzeroCorrection c ∧ c.remainderBudget ≤ c.coefficientBudget ∧
      c.coefficientBudget ≤ totalCorrectionBudget c := by
  refine ⟨h.1, h.2, ?_⟩
  unfold totalCorrectionBudget
  omega

theorem coefficient_le_total (c : CharlierCorrection) :
    c.coefficientBudget ≤ totalCorrectionBudget c := by
  unfold totalCorrectionBudget
  omega

def sampleCorrection : CharlierCorrection :=
  { order := 2, coefficientBudget := 9, remainderBudget := 4 }

example : correctionControlled sampleCorrection := by
  norm_num [correctionControlled, nonzeroCorrection, sampleCorrection]

example : totalCorrectionBudget sampleCorrection = 13 := by
  native_decide

/-- Finite executable readiness audit for Poisson-Charlier corrections. -/
def charlierCorrectionListReady
    (corrections : List CharlierCorrection) : Bool :=
  corrections.all fun c => 0 < c.order && c.remainderBudget ≤ c.coefficientBudget

theorem charlierCorrectionList_readyWindow :
    charlierCorrectionListReady
      [{ order := 1, coefficientBudget := 4, remainderBudget := 2 },
       { order := 2, coefficientBudget := 9, remainderBudget := 4 }] = true := by
  unfold charlierCorrectionListReady
  native_decide

structure PoissonCharlierWindow where
  order : ℕ
  coefficientBudget : ℕ
  remainderBudget : ℕ
  correctionMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonCharlierWindow.orderReady (w : PoissonCharlierWindow) : Prop :=
  0 < w.order

def PoissonCharlierWindow.remainderControlled (w : PoissonCharlierWindow) : Prop :=
  w.remainderBudget ≤ w.coefficientBudget + w.slack

def PoissonCharlierWindow.massControlled (w : PoissonCharlierWindow) : Prop :=
  w.correctionMass ≤ w.order * w.coefficientBudget + w.slack

def PoissonCharlierWindow.ready (w : PoissonCharlierWindow) : Prop :=
  w.orderReady ∧ w.remainderControlled ∧ w.massControlled

def PoissonCharlierWindow.certificate (w : PoissonCharlierWindow) : ℕ :=
  w.order + w.coefficientBudget + w.remainderBudget + w.correctionMass + w.slack

theorem correctionMass_le_certificate (w : PoissonCharlierWindow) :
    w.correctionMass ≤ w.certificate := by
  unfold PoissonCharlierWindow.certificate
  omega

def samplePoissonCharlierWindow : PoissonCharlierWindow :=
  { order := 2, coefficientBudget := 9, remainderBudget := 4, correctionMass := 12, slack := 0 }

example : samplePoissonCharlierWindow.ready := by
  norm_num [samplePoissonCharlierWindow, PoissonCharlierWindow.ready,
    PoissonCharlierWindow.orderReady, PoissonCharlierWindow.remainderControlled,
    PoissonCharlierWindow.massControlled]

/-- A refinement certificate for Poisson-Charlier correction windows. -/
structure PoissonCharlierCertificate where
  orderWindow : ℕ
  coefficientWindow : ℕ
  remainderWindow : ℕ
  correctionMassWindow : ℕ
  slack : ℕ

/-- Correction mass and remainder are controlled by order and coefficient budget. -/
def poissonCharlierCertificateControlled
    (w : PoissonCharlierCertificate) : Prop :=
  0 < w.orderWindow ∧
    w.remainderWindow ≤ w.coefficientWindow + w.slack ∧
      w.correctionMassWindow ≤ w.orderWindow * w.coefficientWindow + w.slack

/-- Readiness for a Poisson-Charlier certificate. -/
def poissonCharlierCertificateReady
    (w : PoissonCharlierCertificate) : Prop :=
  poissonCharlierCertificateControlled w ∧
    w.correctionMassWindow ≤
      w.orderWindow + w.coefficientWindow + w.remainderWindow +
        w.correctionMassWindow + w.slack

/-- Total size of a Poisson-Charlier certificate. -/
def poissonCharlierCertificateSize
    (w : PoissonCharlierCertificate) : ℕ :=
  w.orderWindow + w.coefficientWindow + w.remainderWindow +
    w.correctionMassWindow + w.slack

theorem poissonCharlierCertificate_mass_le_size
    (w : PoissonCharlierCertificate)
    (h : poissonCharlierCertificateReady w) :
    w.correctionMassWindow ≤ poissonCharlierCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold poissonCharlierCertificateSize
  omega

def samplePoissonCharlierCertificate :
    PoissonCharlierCertificate where
  orderWindow := 2
  coefficientWindow := 9
  remainderWindow := 4
  correctionMassWindow := 12
  slack := 0

example :
    poissonCharlierCertificateReady samplePoissonCharlierCertificate := by
  norm_num [poissonCharlierCertificateReady,
    poissonCharlierCertificateControlled, samplePoissonCharlierCertificate]

example :
    samplePoissonCharlierCertificate.correctionMassWindow ≤
      poissonCharlierCertificateSize samplePoissonCharlierCertificate := by
  apply poissonCharlierCertificate_mass_le_size
  norm_num [poissonCharlierCertificateReady,
    poissonCharlierCertificateControlled, samplePoissonCharlierCertificate]

/-- A refinement certificate with the Poisson-Charlier budget separated from size. -/
structure PoissonCharlierRefinementCertificate where
  orderWindow : ℕ
  coefficientWindow : ℕ
  remainderWindow : ℕ
  correctionMassWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonCharlierRefinementCertificate.correctionControlled
    (cert : PoissonCharlierRefinementCertificate) : Prop :=
  0 < cert.orderWindow ∧
    cert.remainderWindow ≤ cert.coefficientWindow + cert.slack ∧
      cert.correctionMassWindow ≤ cert.orderWindow * cert.coefficientWindow + cert.slack

def PoissonCharlierRefinementCertificate.budgetControlled
    (cert : PoissonCharlierRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.orderWindow + cert.coefficientWindow + cert.remainderWindow +
      cert.correctionMassWindow + cert.slack

def poissonCharlierRefinementReady
    (cert : PoissonCharlierRefinementCertificate) : Prop :=
  cert.correctionControlled ∧ cert.budgetControlled

def PoissonCharlierRefinementCertificate.size
    (cert : PoissonCharlierRefinementCertificate) : ℕ :=
  cert.orderWindow + cert.coefficientWindow + cert.remainderWindow +
    cert.correctionMassWindow + cert.slack

theorem poissonCharlier_certificateBudgetWindow_le_size
    (cert : PoissonCharlierRefinementCertificate)
    (h : poissonCharlierRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePoissonCharlierRefinementCertificate :
    PoissonCharlierRefinementCertificate :=
  { orderWindow := 2, coefficientWindow := 9, remainderWindow := 4,
    correctionMassWindow := 12, certificateBudgetWindow := 27, slack := 0 }

example :
    poissonCharlierRefinementReady samplePoissonCharlierRefinementCertificate := by
  norm_num [poissonCharlierRefinementReady,
    PoissonCharlierRefinementCertificate.correctionControlled,
    PoissonCharlierRefinementCertificate.budgetControlled,
    samplePoissonCharlierRefinementCertificate]

example :
    samplePoissonCharlierRefinementCertificate.certificateBudgetWindow ≤
      samplePoissonCharlierRefinementCertificate.size := by
  apply poissonCharlier_certificateBudgetWindow_le_size
  norm_num [poissonCharlierRefinementReady,
    PoissonCharlierRefinementCertificate.correctionControlled,
    PoissonCharlierRefinementCertificate.budgetControlled,
    samplePoissonCharlierRefinementCertificate]


structure PoissonCharlierSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonCharlierSchemasBudgetCertificate.controlled
    (c : PoissonCharlierSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def PoissonCharlierSchemasBudgetCertificate.budgetControlled
    (c : PoissonCharlierSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PoissonCharlierSchemasBudgetCertificate.Ready
    (c : PoissonCharlierSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PoissonCharlierSchemasBudgetCertificate.size
    (c : PoissonCharlierSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem poissonCharlierSchemas_budgetCertificate_le_size
    (c : PoissonCharlierSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePoissonCharlierSchemasBudgetCertificate :
    PoissonCharlierSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : samplePoissonCharlierSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonCharlierSchemasBudgetCertificate.controlled,
      samplePoissonCharlierSchemasBudgetCertificate]
  · norm_num [PoissonCharlierSchemasBudgetCertificate.budgetControlled,
      samplePoissonCharlierSchemasBudgetCertificate]

example :
    samplePoissonCharlierSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonCharlierSchemasBudgetCertificate.size := by
  apply poissonCharlierSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PoissonCharlierSchemasBudgetCertificate.controlled,
      samplePoissonCharlierSchemasBudgetCertificate]
  · norm_num [PoissonCharlierSchemasBudgetCertificate.budgetControlled,
      samplePoissonCharlierSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePoissonCharlierSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonCharlierSchemasBudgetCertificate.controlled,
      samplePoissonCharlierSchemasBudgetCertificate]
  · norm_num [PoissonCharlierSchemasBudgetCertificate.budgetControlled,
      samplePoissonCharlierSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePoissonCharlierSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonCharlierSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List PoissonCharlierSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePoissonCharlierSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    samplePoissonCharlierSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.PoissonCharlierSchemas
