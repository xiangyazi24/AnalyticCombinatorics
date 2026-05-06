import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Additional labelled constructions.

Finite bookkeeping for pointing, marking, rooting, colouring, and weighted
labelled construction variants.
-/

namespace AnalyticCombinatorics.PartA.Ch2.AdditionalLabelledConstructions

/-- Labelled pointing: each labelled object of size `n` has `n` pointed variants. -/
def labelledPointingCount (objects : ℕ → ℕ) (n : ℕ) : ℕ :=
  n * objects n

/-- Rooting certificate for a labelled object family. -/
def labelledRootingCount (objects : ℕ → ℕ) (n : ℕ) : ℕ :=
  if n = 0 then 0 else n * objects n

/-- Finite audit that labelled pointing and rooting stay in the same envelope. -/
def labelledVariantEnvelopeCheck
    (objects envelope : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    labelledPointingCount objects n ≤ n * envelope n ∧
      labelledRootingCount objects n ≤ n * envelope n

theorem labelledVariantEnvelope_constant :
    labelledVariantEnvelopeCheck (fun _ => 1) (fun _ => 1) 16 = true := by
  unfold labelledVariantEnvelopeCheck labelledPointingCount labelledRootingCount
  native_decide

structure AdditionalLabelledConstructionData where
  labelledAtoms : ℕ
  markerTypes : ℕ
  variantWindow : ℕ
  constructionSlack : ℕ
deriving DecidableEq, Repr

def additionalLabelledConstructionReady
    (d : AdditionalLabelledConstructionData) : Prop :=
  0 < d.labelledAtoms ∧
    d.variantWindow ≤ d.labelledAtoms + d.markerTypes + d.constructionSlack

def additionalLabelledConstructionBudget
    (d : AdditionalLabelledConstructionData) : ℕ :=
  d.labelledAtoms + d.markerTypes + d.variantWindow + d.constructionSlack

theorem variantWindow_le_budget (d : AdditionalLabelledConstructionData) :
    d.variantWindow ≤ additionalLabelledConstructionBudget d := by
  unfold additionalLabelledConstructionBudget
  omega

def sampleAdditionalLabelledConstructionData :
    AdditionalLabelledConstructionData :=
  { labelledAtoms := 5, markerTypes := 3, variantWindow := 8,
    constructionSlack := 1 }

example : additionalLabelledConstructionReady
    sampleAdditionalLabelledConstructionData := by
  norm_num [additionalLabelledConstructionReady,
    sampleAdditionalLabelledConstructionData]

structure AdditionalLabelledConstructionsBudgetCertificate where
  atomWindow : ℕ
  markerWindow : ℕ
  variantWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AdditionalLabelledConstructionsBudgetCertificate.controlled
    (c : AdditionalLabelledConstructionsBudgetCertificate) : Prop :=
  0 < c.atomWindow ∧ c.variantWindow ≤ c.atomWindow + c.markerWindow + c.slack

def AdditionalLabelledConstructionsBudgetCertificate.budgetControlled
    (c : AdditionalLabelledConstructionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.atomWindow + c.markerWindow + c.variantWindow + c.slack

def AdditionalLabelledConstructionsBudgetCertificate.Ready
    (c : AdditionalLabelledConstructionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AdditionalLabelledConstructionsBudgetCertificate.size
    (c : AdditionalLabelledConstructionsBudgetCertificate) : ℕ :=
  c.atomWindow + c.markerWindow + c.variantWindow + c.slack

theorem additionalLabelledConstructions_budgetCertificate_le_size
    (c : AdditionalLabelledConstructionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAdditionalLabelledConstructionsBudgetCertificate :
    AdditionalLabelledConstructionsBudgetCertificate :=
  { atomWindow := 5
    markerWindow := 3
    variantWindow := 8
    certificateBudgetWindow := 17
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAdditionalLabelledConstructionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AdditionalLabelledConstructionsBudgetCertificate.controlled,
      sampleAdditionalLabelledConstructionsBudgetCertificate]
  · norm_num [AdditionalLabelledConstructionsBudgetCertificate.budgetControlled,
      sampleAdditionalLabelledConstructionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAdditionalLabelledConstructionsBudgetCertificate.certificateBudgetWindow ≤
      sampleAdditionalLabelledConstructionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAdditionalLabelledConstructionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AdditionalLabelledConstructionsBudgetCertificate.controlled,
      sampleAdditionalLabelledConstructionsBudgetCertificate]
  · norm_num [AdditionalLabelledConstructionsBudgetCertificate.budgetControlled,
      sampleAdditionalLabelledConstructionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AdditionalLabelledConstructionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAdditionalLabelledConstructionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAdditionalLabelledConstructionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.AdditionalLabelledConstructions
