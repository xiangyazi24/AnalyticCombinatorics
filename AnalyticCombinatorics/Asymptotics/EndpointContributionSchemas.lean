import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Endpoint contribution schema bookkeeping.

The file records endpoint order, local scale, and interior error budgets for
endpoint-dominated asymptotic integrals.
-/

namespace AnalyticCombinatorics.Asymptotics.EndpointContributionSchemas

structure EndpointData where
  endpointOrder : ℕ
  localScale : ℕ
  interiorError : ℕ
deriving DecidableEq, Repr

def endpointNondegenerate (d : EndpointData) : Prop :=
  0 < d.endpointOrder ∧ 0 < d.localScale

def endpointBudget (d : EndpointData) : ℕ :=
  d.endpointOrder * d.localScale + d.interiorError

def endpointReady (d : EndpointData) : Prop :=
  endpointNondegenerate d

theorem endpointReady.nondegenerate {d : EndpointData}
    (h : endpointReady d) :
    endpointNondegenerate d ∧ d.endpointOrder ≤ endpointBudget d := by
  refine ⟨h, ?_⟩
  unfold endpointReady endpointNondegenerate at h
  unfold endpointBudget
  have hmul : d.endpointOrder ≤ d.endpointOrder * d.localScale := by
    nth_rewrite 1 [← Nat.mul_one d.endpointOrder]
    exact Nat.mul_le_mul_left d.endpointOrder h.2
  omega

theorem endpointBudget_ge_error (d : EndpointData) :
    d.interiorError ≤ endpointBudget d := by
  unfold endpointBudget
  omega

def sampleEndpoint : EndpointData :=
  { endpointOrder := 2, localScale := 6, interiorError := 5 }

example : endpointReady sampleEndpoint := by
  norm_num [endpointReady, endpointNondegenerate, sampleEndpoint]

example : endpointBudget sampleEndpoint = 17 := by
  native_decide

/-- Finite executable readiness audit for endpoint contribution data. -/
def endpointDataListReady (data : List EndpointData) : Bool :=
  data.all fun d => 0 < d.endpointOrder && 0 < d.localScale

theorem endpointDataList_readyWindow :
    endpointDataListReady
      [{ endpointOrder := 1, localScale := 4, interiorError := 2 },
       { endpointOrder := 2, localScale := 6, interiorError := 5 }] = true := by
  unfold endpointDataListReady
  native_decide

structure EndpointContributionWindow where
  orderWindow : ℕ
  localScaleWindow : ℕ
  interiorErrorWindow : ℕ
  contributionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EndpointContributionWindow.errorControlled
    (w : EndpointContributionWindow) : Prop :=
  w.interiorErrorWindow ≤ w.orderWindow * w.localScaleWindow + w.slack

def endpointContributionWindowReady (w : EndpointContributionWindow) : Prop :=
  0 < w.orderWindow ∧ 0 < w.localScaleWindow ∧ w.errorControlled ∧
    w.contributionBudget ≤ w.orderWindow * w.localScaleWindow + w.interiorErrorWindow + w.slack

def EndpointContributionWindow.certificate (w : EndpointContributionWindow) : ℕ :=
  w.orderWindow * w.localScaleWindow + w.interiorErrorWindow + w.contributionBudget + w.slack

theorem endpointContribution_budget_le_certificate
    (w : EndpointContributionWindow) :
    w.contributionBudget ≤ w.certificate := by
  unfold EndpointContributionWindow.certificate
  omega

def sampleEndpointContributionWindow : EndpointContributionWindow :=
  { orderWindow := 2, localScaleWindow := 6, interiorErrorWindow := 5,
    contributionBudget := 18, slack := 1 }

example : endpointContributionWindowReady sampleEndpointContributionWindow := by
  norm_num [endpointContributionWindowReady,
    EndpointContributionWindow.errorControlled, sampleEndpointContributionWindow]

/-- A refinement certificate for endpoint contribution windows. -/
structure EndpointContributionCertificate where
  orderWindow : ℕ
  localScaleWindow : ℕ
  interiorErrorWindow : ℕ
  contributionWindow : ℕ
  slack : ℕ

/-- Endpoint local scale controls interior error and contribution budget. -/
def endpointContributionCertificateControlled
    (w : EndpointContributionCertificate) : Prop :=
  0 < w.orderWindow ∧
    0 < w.localScaleWindow ∧
      w.interiorErrorWindow ≤ w.orderWindow * w.localScaleWindow + w.slack ∧
        w.contributionWindow ≤
          w.orderWindow * w.localScaleWindow + w.interiorErrorWindow + w.slack

/-- Readiness for an endpoint contribution certificate. -/
def endpointContributionCertificateReady
    (w : EndpointContributionCertificate) : Prop :=
  endpointContributionCertificateControlled w ∧
    w.contributionWindow ≤
      w.orderWindow * w.localScaleWindow + w.interiorErrorWindow +
        w.contributionWindow + w.slack

/-- Total size of an endpoint contribution certificate. -/
def endpointContributionCertificateSize
    (w : EndpointContributionCertificate) : ℕ :=
  w.orderWindow * w.localScaleWindow + w.interiorErrorWindow +
    w.contributionWindow + w.slack

theorem endpointContributionCertificate_contribution_le_size
    (w : EndpointContributionCertificate)
    (h : endpointContributionCertificateReady w) :
    w.contributionWindow ≤ endpointContributionCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold endpointContributionCertificateSize
  omega

def sampleEndpointContributionCertificate :
    EndpointContributionCertificate where
  orderWindow := 2
  localScaleWindow := 6
  interiorErrorWindow := 5
  contributionWindow := 18
  slack := 1

example :
    endpointContributionCertificateReady
      sampleEndpointContributionCertificate := by
  norm_num [endpointContributionCertificateReady,
    endpointContributionCertificateControlled, sampleEndpointContributionCertificate]

example :
    sampleEndpointContributionCertificate.contributionWindow ≤
      endpointContributionCertificateSize sampleEndpointContributionCertificate := by
  apply endpointContributionCertificate_contribution_le_size
  norm_num [endpointContributionCertificateReady,
    endpointContributionCertificateControlled, sampleEndpointContributionCertificate]

/-- A refinement certificate with the endpoint-contribution budget separated from size. -/
structure EndpointContributionRefinementCertificate where
  orderWindow : ℕ
  localScaleWindow : ℕ
  interiorErrorWindow : ℕ
  contributionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EndpointContributionRefinementCertificate.endpointControlled
    (cert : EndpointContributionRefinementCertificate) : Prop :=
  0 < cert.orderWindow ∧
    0 < cert.localScaleWindow ∧
      cert.interiorErrorWindow ≤ cert.orderWindow * cert.localScaleWindow + cert.slack ∧
        cert.contributionWindow ≤
          cert.orderWindow * cert.localScaleWindow + cert.interiorErrorWindow + cert.slack

def EndpointContributionRefinementCertificate.budgetControlled
    (cert : EndpointContributionRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.orderWindow * cert.localScaleWindow + cert.interiorErrorWindow +
      cert.contributionWindow + cert.slack

def endpointContributionRefinementReady
    (cert : EndpointContributionRefinementCertificate) : Prop :=
  cert.endpointControlled ∧ cert.budgetControlled

def EndpointContributionRefinementCertificate.size
    (cert : EndpointContributionRefinementCertificate) : ℕ :=
  cert.orderWindow * cert.localScaleWindow + cert.interiorErrorWindow +
    cert.contributionWindow + cert.slack

theorem endpointContribution_certificateBudgetWindow_le_size
    (cert : EndpointContributionRefinementCertificate)
    (h : endpointContributionRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEndpointContributionRefinementCertificate :
    EndpointContributionRefinementCertificate :=
  { orderWindow := 2, localScaleWindow := 6, interiorErrorWindow := 5,
    contributionWindow := 18, certificateBudgetWindow := 36, slack := 1 }

example :
    endpointContributionRefinementReady
      sampleEndpointContributionRefinementCertificate := by
  norm_num [endpointContributionRefinementReady,
    EndpointContributionRefinementCertificate.endpointControlled,
    EndpointContributionRefinementCertificate.budgetControlled,
    sampleEndpointContributionRefinementCertificate]

example :
    sampleEndpointContributionRefinementCertificate.certificateBudgetWindow ≤
      sampleEndpointContributionRefinementCertificate.size := by
  apply endpointContribution_certificateBudgetWindow_le_size
  norm_num [endpointContributionRefinementReady,
    EndpointContributionRefinementCertificate.endpointControlled,
    EndpointContributionRefinementCertificate.budgetControlled,
    sampleEndpointContributionRefinementCertificate]


structure EndpointContributionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EndpointContributionSchemasBudgetCertificate.controlled
    (c : EndpointContributionSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def EndpointContributionSchemasBudgetCertificate.budgetControlled
    (c : EndpointContributionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def EndpointContributionSchemasBudgetCertificate.Ready
    (c : EndpointContributionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EndpointContributionSchemasBudgetCertificate.size
    (c : EndpointContributionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem endpointContributionSchemas_budgetCertificate_le_size
    (c : EndpointContributionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEndpointContributionSchemasBudgetCertificate :
    EndpointContributionSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleEndpointContributionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EndpointContributionSchemasBudgetCertificate.controlled,
      sampleEndpointContributionSchemasBudgetCertificate]
  · norm_num [EndpointContributionSchemasBudgetCertificate.budgetControlled,
      sampleEndpointContributionSchemasBudgetCertificate]

example :
    sampleEndpointContributionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEndpointContributionSchemasBudgetCertificate.size := by
  apply endpointContributionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [EndpointContributionSchemasBudgetCertificate.controlled,
      sampleEndpointContributionSchemasBudgetCertificate]
  · norm_num [EndpointContributionSchemasBudgetCertificate.budgetControlled,
      sampleEndpointContributionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleEndpointContributionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EndpointContributionSchemasBudgetCertificate.controlled,
      sampleEndpointContributionSchemasBudgetCertificate]
  · norm_num [EndpointContributionSchemasBudgetCertificate.budgetControlled,
      sampleEndpointContributionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleEndpointContributionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEndpointContributionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List EndpointContributionSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEndpointContributionSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleEndpointContributionSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.EndpointContributionSchemas
