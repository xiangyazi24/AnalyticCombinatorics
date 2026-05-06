import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Additional constructions for parameter marking.

Finite bookkeeping for auxiliary parameter constructions beyond the basic
bivariate schemas.
-/

namespace AnalyticCombinatorics.PartA.Ch3.AdditionalParameterConstructions

/-- Marked construction: each object of size `n` has `parameter n` marks. -/
def markedParameterCount (objects parameter : ℕ → ℕ) (n : ℕ) : ℕ :=
  objects n * parameter n

/-- Pointed parameter count, bounded by size for size-bounded parameters. -/
def pointedParameterEnvelopeCheck
    (objects parameter : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    parameter n ≤ n ∧ markedParameterCount objects parameter n ≤ n * objects n

theorem sizeParameter_markedWindow :
    pointedParameterEnvelopeCheck (fun _ => 1) (fun n => n) 16 = true := by
  unfold pointedParameterEnvelopeCheck markedParameterCount
  native_decide

/-- Prefix total of a marked parameter construction. -/
def markedParameterPrefix
    (objects parameter : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total n => total + markedParameterCount objects parameter n) 0

theorem sizeParameter_markedPrefixWindow :
    markedParameterPrefix (fun _ => 1) (fun n => n) 5 = 15 := by
  unfold markedParameterPrefix markedParameterCount
  native_decide

structure AdditionalParameterConstructionData where
  constructionCount : ℕ
  markerCount : ℕ
  transferDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def additionalParameterConstructionReady
    (d : AdditionalParameterConstructionData) : Prop :=
  0 < d.constructionCount ∧
    d.markerCount ≤ d.constructionCount + d.transferDepth + d.slack

def additionalParameterConstructionBudget
    (d : AdditionalParameterConstructionData) : ℕ :=
  d.constructionCount + d.markerCount + d.transferDepth + d.slack

theorem markerCount_le_additionalBudget
    (d : AdditionalParameterConstructionData) :
    d.markerCount ≤ additionalParameterConstructionBudget d := by
  unfold additionalParameterConstructionBudget
  omega

def sampleAdditionalParameterConstructionData :
    AdditionalParameterConstructionData :=
  { constructionCount := 5, markerCount := 7, transferDepth := 3, slack := 1 }

example :
    additionalParameterConstructionReady
      sampleAdditionalParameterConstructionData := by
  norm_num
    [additionalParameterConstructionReady,
      sampleAdditionalParameterConstructionData]

structure AdditionalParameterConstructionsBudgetCertificate where
  constructionWindow : ℕ
  markerWindow : ℕ
  transferWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AdditionalParameterConstructionsBudgetCertificate.controlled
    (c : AdditionalParameterConstructionsBudgetCertificate) : Prop :=
  0 < c.constructionWindow ∧
    c.markerWindow ≤ c.constructionWindow + c.transferWindow + c.slack

def AdditionalParameterConstructionsBudgetCertificate.budgetControlled
    (c : AdditionalParameterConstructionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.constructionWindow + c.markerWindow + c.transferWindow + c.slack

def AdditionalParameterConstructionsBudgetCertificate.Ready
    (c : AdditionalParameterConstructionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AdditionalParameterConstructionsBudgetCertificate.size
    (c : AdditionalParameterConstructionsBudgetCertificate) : ℕ :=
  c.constructionWindow + c.markerWindow + c.transferWindow + c.slack

theorem additionalParameterConstructions_budgetCertificate_le_size
    (c : AdditionalParameterConstructionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAdditionalParameterConstructionsBudgetCertificate :
    AdditionalParameterConstructionsBudgetCertificate :=
  { constructionWindow := 5
    markerWindow := 7
    transferWindow := 3
    certificateBudgetWindow := 16
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAdditionalParameterConstructionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AdditionalParameterConstructionsBudgetCertificate.controlled,
      sampleAdditionalParameterConstructionsBudgetCertificate]
  · norm_num [AdditionalParameterConstructionsBudgetCertificate.budgetControlled,
      sampleAdditionalParameterConstructionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAdditionalParameterConstructionsBudgetCertificate.certificateBudgetWindow ≤
      sampleAdditionalParameterConstructionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAdditionalParameterConstructionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AdditionalParameterConstructionsBudgetCertificate.controlled,
      sampleAdditionalParameterConstructionsBudgetCertificate]
  · norm_num [AdditionalParameterConstructionsBudgetCertificate.budgetControlled,
      sampleAdditionalParameterConstructionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AdditionalParameterConstructionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAdditionalParameterConstructionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAdditionalParameterConstructionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.AdditionalParameterConstructions
