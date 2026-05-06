import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Endpoint saddle schemas.

The finite schema records endpoint width, saddle scale, and truncation
slack.
-/

namespace AnalyticCombinatorics.PartB.Ch8.EndpointSaddleSchemas

structure EndpointSaddleData where
  endpointWidth : ℕ
  saddleScale : ℕ
  truncationSlack : ℕ
deriving DecidableEq, Repr

def saddleScalePositive (d : EndpointSaddleData) : Prop :=
  0 < d.saddleScale

def endpointWidthControlled (d : EndpointSaddleData) : Prop :=
  d.endpointWidth ≤ d.saddleScale + d.truncationSlack

def endpointSaddleReady (d : EndpointSaddleData) : Prop :=
  saddleScalePositive d ∧ endpointWidthControlled d

def endpointSaddleBudget (d : EndpointSaddleData) : ℕ :=
  d.endpointWidth + d.saddleScale + d.truncationSlack

theorem endpointSaddleReady.scale {d : EndpointSaddleData}
    (h : endpointSaddleReady d) :
    saddleScalePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem endpointWidth_le_endpointSaddleBudget
    (d : EndpointSaddleData) :
    d.endpointWidth ≤ endpointSaddleBudget d := by
  unfold endpointSaddleBudget
  omega

def sampleEndpointSaddleData : EndpointSaddleData :=
  { endpointWidth := 6, saddleScale := 4, truncationSlack := 3 }

example : endpointSaddleReady sampleEndpointSaddleData := by
  norm_num [endpointSaddleReady, saddleScalePositive]
  norm_num [endpointWidthControlled, sampleEndpointSaddleData]

example : endpointSaddleBudget sampleEndpointSaddleData = 13 := by
  native_decide

structure EndpointSaddleBudgetCertificate where
  endpointWidthWindow : ℕ
  saddleScaleWindow : ℕ
  truncationSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EndpointSaddleBudgetCertificate.controlled
    (c : EndpointSaddleBudgetCertificate) : Prop :=
  0 < c.saddleScaleWindow ∧
    c.endpointWidthWindow ≤ c.saddleScaleWindow + c.truncationSlackWindow + c.slack

def EndpointSaddleBudgetCertificate.budgetControlled
    (c : EndpointSaddleBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.endpointWidthWindow + c.saddleScaleWindow + c.truncationSlackWindow + c.slack

def EndpointSaddleBudgetCertificate.Ready
    (c : EndpointSaddleBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EndpointSaddleBudgetCertificate.size
    (c : EndpointSaddleBudgetCertificate) : ℕ :=
  c.endpointWidthWindow + c.saddleScaleWindow + c.truncationSlackWindow + c.slack

theorem endpointSaddle_budgetCertificate_le_size
    (c : EndpointSaddleBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEndpointSaddleBudgetCertificate :
    EndpointSaddleBudgetCertificate :=
  { endpointWidthWindow := 6
    saddleScaleWindow := 4
    truncationSlackWindow := 3
    certificateBudgetWindow := 14
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleEndpointSaddleBudgetCertificate.Ready := by
  constructor
  · norm_num [EndpointSaddleBudgetCertificate.controlled,
      sampleEndpointSaddleBudgetCertificate]
  · norm_num [EndpointSaddleBudgetCertificate.budgetControlled,
      sampleEndpointSaddleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleEndpointSaddleBudgetCertificate.certificateBudgetWindow ≤
      sampleEndpointSaddleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleEndpointSaddleBudgetCertificate.Ready := by
  constructor
  · norm_num [EndpointSaddleBudgetCertificate.controlled,
      sampleEndpointSaddleBudgetCertificate]
  · norm_num [EndpointSaddleBudgetCertificate.budgetControlled,
      sampleEndpointSaddleBudgetCertificate]

example :
    sampleEndpointSaddleBudgetCertificate.certificateBudgetWindow ≤
      sampleEndpointSaddleBudgetCertificate.size := by
  apply endpointSaddle_budgetCertificate_le_size
  constructor
  · norm_num [EndpointSaddleBudgetCertificate.controlled,
      sampleEndpointSaddleBudgetCertificate]
  · norm_num [EndpointSaddleBudgetCertificate.budgetControlled,
      sampleEndpointSaddleBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List EndpointSaddleBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleEndpointSaddleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleEndpointSaddleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.EndpointSaddleSchemas
