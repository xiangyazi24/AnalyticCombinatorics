import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Stable domain attraction schemas.

This module records finite bookkeeping for stable domain-attraction windows.
-/

namespace AnalyticCombinatorics.AppC.StableDomainAttractionSchemas

structure StableDomainAttractionData where
  normalizationScale : ℕ
  tailWindow : ℕ
  attractionSlack : ℕ
deriving DecidableEq, Repr

def hasNormalizationScale (d : StableDomainAttractionData) : Prop :=
  0 < d.normalizationScale

def tailWindowControlled (d : StableDomainAttractionData) : Prop :=
  d.tailWindow ≤ d.normalizationScale + d.attractionSlack

def stableDomainAttractionReady
    (d : StableDomainAttractionData) : Prop :=
  hasNormalizationScale d ∧ tailWindowControlled d

def stableDomainAttractionBudget
    (d : StableDomainAttractionData) : ℕ :=
  d.normalizationScale + d.tailWindow + d.attractionSlack

theorem stableDomainAttractionReady.hasNormalizationScale
    {d : StableDomainAttractionData}
    (h : stableDomainAttractionReady d) :
    hasNormalizationScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem tailWindow_le_budget (d : StableDomainAttractionData) :
    d.tailWindow ≤ stableDomainAttractionBudget d := by
  unfold stableDomainAttractionBudget
  omega

def sampleStableDomainAttractionData : StableDomainAttractionData :=
  { normalizationScale := 6, tailWindow := 8, attractionSlack := 3 }

example : stableDomainAttractionReady sampleStableDomainAttractionData := by
  norm_num [stableDomainAttractionReady, hasNormalizationScale]
  norm_num [tailWindowControlled, sampleStableDomainAttractionData]

example :
    stableDomainAttractionBudget sampleStableDomainAttractionData = 17 := by
  native_decide

structure StableDomainAttractionWindow where
  normalizationWindow : ℕ
  tailWindow : ℕ
  attractionSlack : ℕ
  attractionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StableDomainAttractionWindow.tailControlled
    (w : StableDomainAttractionWindow) : Prop :=
  w.tailWindow ≤ w.normalizationWindow + w.attractionSlack + w.slack

def stableDomainAttractionWindowReady (w : StableDomainAttractionWindow) : Prop :=
  0 < w.normalizationWindow ∧ w.tailControlled ∧
    w.attractionBudget ≤ w.normalizationWindow + w.tailWindow + w.slack

def StableDomainAttractionWindow.certificate
    (w : StableDomainAttractionWindow) : ℕ :=
  w.normalizationWindow + w.tailWindow + w.attractionSlack + w.attractionBudget + w.slack

theorem stableDomainAttraction_attractionBudget_le_certificate
    (w : StableDomainAttractionWindow) :
    w.attractionBudget ≤ w.certificate := by
  unfold StableDomainAttractionWindow.certificate
  omega

def sampleStableDomainAttractionWindow : StableDomainAttractionWindow :=
  { normalizationWindow := 5, tailWindow := 7, attractionSlack := 2,
    attractionBudget := 14, slack := 2 }

example : stableDomainAttractionWindowReady sampleStableDomainAttractionWindow := by
  norm_num [stableDomainAttractionWindowReady,
    StableDomainAttractionWindow.tailControlled, sampleStableDomainAttractionWindow]


structure StableDomainAttractionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StableDomainAttractionSchemasBudgetCertificate.controlled
    (c : StableDomainAttractionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def StableDomainAttractionSchemasBudgetCertificate.budgetControlled
    (c : StableDomainAttractionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def StableDomainAttractionSchemasBudgetCertificate.Ready
    (c : StableDomainAttractionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StableDomainAttractionSchemasBudgetCertificate.size
    (c : StableDomainAttractionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem stableDomainAttractionSchemas_budgetCertificate_le_size
    (c : StableDomainAttractionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleStableDomainAttractionSchemasBudgetCertificate :
    StableDomainAttractionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleStableDomainAttractionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [StableDomainAttractionSchemasBudgetCertificate.controlled,
      sampleStableDomainAttractionSchemasBudgetCertificate]
  · norm_num [StableDomainAttractionSchemasBudgetCertificate.budgetControlled,
      sampleStableDomainAttractionSchemasBudgetCertificate]

example : sampleStableDomainAttractionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [StableDomainAttractionSchemasBudgetCertificate.controlled,
      sampleStableDomainAttractionSchemasBudgetCertificate]
  · norm_num [StableDomainAttractionSchemasBudgetCertificate.budgetControlled,
      sampleStableDomainAttractionSchemasBudgetCertificate]

example :
    sampleStableDomainAttractionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleStableDomainAttractionSchemasBudgetCertificate.size := by
  apply stableDomainAttractionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [StableDomainAttractionSchemasBudgetCertificate.controlled,
      sampleStableDomainAttractionSchemasBudgetCertificate]
  · norm_num [StableDomainAttractionSchemasBudgetCertificate.budgetControlled,
      sampleStableDomainAttractionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleStableDomainAttractionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleStableDomainAttractionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List StableDomainAttractionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleStableDomainAttractionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleStableDomainAttractionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.StableDomainAttractionSchemas
