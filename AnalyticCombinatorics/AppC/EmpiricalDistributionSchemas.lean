import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Empirical distribution schema bookkeeping.

The finite data records sample size, support budget, and discrepancy.
-/

namespace AnalyticCombinatorics.AppC.EmpiricalDistributionSchemas

structure EmpiricalDatum where
  sampleSize : ℕ
  supportBudget : ℕ
  discrepancyBudget : ℕ
deriving DecidableEq, Repr

def nonemptySample (d : EmpiricalDatum) : Prop :=
  0 < d.sampleSize

def supportControlled (d : EmpiricalDatum) : Prop :=
  d.supportBudget ≤ d.sampleSize + d.discrepancyBudget

def empiricalReady (d : EmpiricalDatum) : Prop :=
  nonemptySample d ∧ supportControlled d

def empiricalBudget (d : EmpiricalDatum) : ℕ :=
  d.sampleSize + d.supportBudget + d.discrepancyBudget

theorem empiricalReady.sample {d : EmpiricalDatum}
    (h : empiricalReady d) :
    nonemptySample d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem sampleSize_le_empiricalBudget (d : EmpiricalDatum) :
    d.sampleSize ≤ empiricalBudget d := by
  unfold empiricalBudget
  omega

def sampleEmpirical : EmpiricalDatum :=
  { sampleSize := 10, supportBudget := 7, discrepancyBudget := 2 }

example : empiricalReady sampleEmpirical := by
  norm_num [empiricalReady, nonemptySample, supportControlled, sampleEmpirical]

example : empiricalBudget sampleEmpirical = 19 := by
  native_decide

structure EmpiricalWindow where
  sampleSize : ℕ
  supportBudget : ℕ
  discrepancyBudget : ℕ
  histogramMass : ℕ
deriving DecidableEq, Repr

def EmpiricalWindow.sampleReady (w : EmpiricalWindow) : Prop :=
  0 < w.sampleSize

def EmpiricalWindow.supportReady (w : EmpiricalWindow) : Prop :=
  w.supportBudget ≤ w.sampleSize + w.discrepancyBudget

def EmpiricalWindow.histogramControlled (w : EmpiricalWindow) : Prop :=
  w.histogramMass ≤ w.sampleSize + w.discrepancyBudget

def EmpiricalWindow.ready (w : EmpiricalWindow) : Prop :=
  w.sampleReady ∧ w.supportReady ∧ w.histogramControlled

def EmpiricalWindow.certificate (w : EmpiricalWindow) : ℕ :=
  w.sampleSize + w.supportBudget + w.discrepancyBudget + w.histogramMass

theorem histogramMass_le_certificate (w : EmpiricalWindow) :
    w.histogramMass ≤ w.certificate := by
  unfold EmpiricalWindow.certificate
  omega

def sampleEmpiricalWindow : EmpiricalWindow :=
  { sampleSize := 10, supportBudget := 7, discrepancyBudget := 2, histogramMass := 10 }

example : sampleEmpiricalWindow.ready := by
  norm_num [sampleEmpiricalWindow, EmpiricalWindow.ready, EmpiricalWindow.sampleReady,
    EmpiricalWindow.supportReady, EmpiricalWindow.histogramControlled]

structure EmpiricalDistributionRefinementWindow where
  sampleWindow : ℕ
  supportWindow : ℕ
  discrepancyWindow : ℕ
  histogramWindow : ℕ
  empiricalBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EmpiricalDistributionRefinementWindow.histogramControlled
    (w : EmpiricalDistributionRefinementWindow) : Prop :=
  w.histogramWindow ≤ w.sampleWindow + w.discrepancyWindow + w.slack

def empiricalDistributionRefinementWindowReady
    (w : EmpiricalDistributionRefinementWindow) : Prop :=
  0 < w.sampleWindow ∧ w.histogramControlled ∧
    w.empiricalBudget ≤ w.sampleWindow + w.supportWindow + w.histogramWindow + w.slack

def EmpiricalDistributionRefinementWindow.certificate
    (w : EmpiricalDistributionRefinementWindow) : ℕ :=
  w.sampleWindow + w.supportWindow + w.discrepancyWindow + w.histogramWindow +
    w.empiricalBudget + w.slack

theorem empiricalDistributionRefinement_budget_le_certificate
    (w : EmpiricalDistributionRefinementWindow) :
    w.empiricalBudget ≤ w.certificate := by
  unfold EmpiricalDistributionRefinementWindow.certificate
  omega

def sampleEmpiricalDistributionRefinementWindow :
    EmpiricalDistributionRefinementWindow :=
  { sampleWindow := 10, supportWindow := 7, discrepancyWindow := 2,
    histogramWindow := 10, empiricalBudget := 28, slack := 1 }

example : empiricalDistributionRefinementWindowReady
    sampleEmpiricalDistributionRefinementWindow := by
  norm_num [empiricalDistributionRefinementWindowReady,
    EmpiricalDistributionRefinementWindow.histogramControlled,
    sampleEmpiricalDistributionRefinementWindow]


structure EmpiricalDistributionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EmpiricalDistributionSchemasBudgetCertificate.controlled
    (c : EmpiricalDistributionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def EmpiricalDistributionSchemasBudgetCertificate.budgetControlled
    (c : EmpiricalDistributionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def EmpiricalDistributionSchemasBudgetCertificate.Ready
    (c : EmpiricalDistributionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EmpiricalDistributionSchemasBudgetCertificate.size
    (c : EmpiricalDistributionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem empiricalDistributionSchemas_budgetCertificate_le_size
    (c : EmpiricalDistributionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEmpiricalDistributionSchemasBudgetCertificate :
    EmpiricalDistributionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleEmpiricalDistributionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EmpiricalDistributionSchemasBudgetCertificate.controlled,
      sampleEmpiricalDistributionSchemasBudgetCertificate]
  · norm_num [EmpiricalDistributionSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalDistributionSchemasBudgetCertificate]

example :
    sampleEmpiricalDistributionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEmpiricalDistributionSchemasBudgetCertificate.size := by
  apply empiricalDistributionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [EmpiricalDistributionSchemasBudgetCertificate.controlled,
      sampleEmpiricalDistributionSchemasBudgetCertificate]
  · norm_num [EmpiricalDistributionSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalDistributionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleEmpiricalDistributionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EmpiricalDistributionSchemasBudgetCertificate.controlled,
      sampleEmpiricalDistributionSchemasBudgetCertificate]
  · norm_num [EmpiricalDistributionSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalDistributionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleEmpiricalDistributionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEmpiricalDistributionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List EmpiricalDistributionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEmpiricalDistributionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleEmpiricalDistributionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.EmpiricalDistributionSchemas
