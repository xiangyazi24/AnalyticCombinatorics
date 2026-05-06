import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Additional constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.AdditionalConstructions

/-- Cauchy product coefficient over a finite prefix. -/
def productCoeff (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + a k * b (n - k)) 0

/-- Pointing construction certificate: each object of size `n` has `n` marks. -/
def pointedCoeff (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  n * a n

/-- Finite construction envelope for products and pointing. -/
def additionalConstructionCheck
    (a b envelope : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    productCoeff a b n ≤ envelope n ∧ pointedCoeff a n ≤ n * envelope n

theorem productCoeff_constant_samples :
    productCoeff (fun _ => 1) (fun _ => 1) 0 = 1 ∧
    productCoeff (fun _ => 1) (fun _ => 1) 1 = 2 ∧
    productCoeff (fun _ => 1) (fun _ => 1) 2 = 3 ∧
    productCoeff (fun _ => 1) (fun _ => 1) 3 = 4 := by
  unfold productCoeff
  native_decide

theorem additionalConstruction_constantWindow :
    additionalConstructionCheck (fun _ => 1) (fun _ => 1) (fun n => n + 1) 12 = true := by
  unfold additionalConstructionCheck productCoeff pointedCoeff
  native_decide

def pointedPrefixSum (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total n => total + pointedCoeff a n) 0

def PointedConstructionWindow (a : ℕ → ℕ) (N total : ℕ) : Prop :=
  pointedPrefixSum a N = total

theorem pointedConstant_prefixWindow :
    PointedConstructionWindow (fun _ => 1) 5 15 := by
  unfold PointedConstructionWindow pointedPrefixSum pointedCoeff
  native_decide

example : productCoeff (fun n => n + 1) (fun _ => 1) 2 = 6 := by
  unfold productCoeff
  native_decide

example : pointedCoeff (fun n => n + 1) 4 = 20 := by
  unfold pointedCoeff
  native_decide

structure AdditionalConstructionsBudgetCertificate where
  constructionWindow : ℕ
  markerWindow : ℕ
  transferWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AdditionalConstructionsBudgetCertificate.controlled
    (c : AdditionalConstructionsBudgetCertificate) : Prop :=
  0 < c.constructionWindow ∧
    c.transferWindow ≤ c.constructionWindow + c.markerWindow + c.slack

def AdditionalConstructionsBudgetCertificate.budgetControlled
    (c : AdditionalConstructionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.constructionWindow + c.markerWindow + c.transferWindow + c.slack

def AdditionalConstructionsBudgetCertificate.Ready
    (c : AdditionalConstructionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AdditionalConstructionsBudgetCertificate.size
    (c : AdditionalConstructionsBudgetCertificate) : ℕ :=
  c.constructionWindow + c.markerWindow + c.transferWindow + c.slack

theorem additionalConstructions_budgetCertificate_le_size
    (c : AdditionalConstructionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAdditionalConstructionsBudgetCertificate :
    AdditionalConstructionsBudgetCertificate :=
  { constructionWindow := 5
    markerWindow := 6
    transferWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAdditionalConstructionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AdditionalConstructionsBudgetCertificate.controlled,
      sampleAdditionalConstructionsBudgetCertificate]
  · norm_num [AdditionalConstructionsBudgetCertificate.budgetControlled,
      sampleAdditionalConstructionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAdditionalConstructionsBudgetCertificate.certificateBudgetWindow ≤
      sampleAdditionalConstructionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAdditionalConstructionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AdditionalConstructionsBudgetCertificate.controlled,
      sampleAdditionalConstructionsBudgetCertificate]
  · norm_num [AdditionalConstructionsBudgetCertificate.budgetControlled,
      sampleAdditionalConstructionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AdditionalConstructionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAdditionalConstructionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAdditionalConstructionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.AdditionalConstructions
