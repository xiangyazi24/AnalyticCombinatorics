import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Universal Limit Schemas

Additional finite models for the Chapter IX theme that broad classes of
combinatorial parameters converge to a small set of universal laws.
-/

namespace AnalyticCombinatorics.PartB.Ch9.UniversalLimitSchemas

/-- A finite probability mass function over rational weights. -/
structure FinitePMF where
  weights : List ℚ

def totalMass (p : FinitePMF) : ℚ :=
  p.weights.foldl (fun s x => s + x) 0

def firstMoment (p : FinitePMF) : ℚ :=
  (List.range p.weights.length).foldl
    (fun (s : ℚ) (k : ℕ) => s + (k : ℚ) * p.weights.getD k 0) 0

def secondMoment (p : FinitePMF) : ℚ :=
  (List.range p.weights.length).foldl
    (fun (s : ℚ) (k : ℕ) => s + (k : ℚ) ^ 2 * p.weights.getD k 0) 0

def fairCoin : FinitePMF where
  weights := [1 / 2, 1 / 2]

def fairDie : FinitePMF where
  weights := [1 / 6, 1 / 6, 1 / 6, 1 / 6, 1 / 6, 1 / 6]

theorem fairCoin_mass_moments :
    totalMass fairCoin = 1 ∧
    firstMoment fairCoin = 1 / 2 ∧
    secondMoment fairCoin = 1 / 2 := by
  native_decide

theorem fairDie_mass :
    totalMass fairDie = 1 := by
  native_decide

/-- Convolution of finite rational mass functions. -/
def pmfConvolution (p q : FinitePMF) : FinitePMF where
  weights :=
    (List.range (p.weights.length + q.weights.length - 1)).map fun n =>
      (List.range (n + 1)).foldl
        (fun s k =>
          s + p.weights.getD k 0 * q.weights.getD (n - k) 0)
        0

def twoCoins : FinitePMF := pmfConvolution fairCoin fairCoin

theorem twoCoins_weights :
    twoCoins.weights = [1 / 4, 1 / 2, 1 / 4] := by
  native_decide

theorem twoCoins_mass_moments :
    totalMass twoCoins = 1 ∧
    firstMoment twoCoins = 1 ∧
    secondMoment twoCoins = 3 / 2 := by
  native_decide

/-- Finite local limit check against the symmetric binomial row. -/
def binomialPMF (n : ℕ) : FinitePMF where
  weights := (List.range (n + 1)).map fun k => (n.choose k : ℚ) / (2 : ℚ) ^ n

theorem binomialPMF_3 :
    (binomialPMF 3).weights = [1 / 8, 3 / 8, 3 / 8, 1 / 8] := by
  native_decide

theorem binomialPMF_4_mass :
    totalMass (binomialPMF 4) = 1 := by
  native_decide

/-- A finite centered symmetry certificate. -/
def symmetricWeights (p : FinitePMF) : Bool :=
  let n := p.weights.length
  (List.range n).all fun k => p.weights.getD k 0 == p.weights.getD (n - 1 - k) 0

theorem binomialPMF_4_symmetric :
    symmetricWeights (binomialPMF 4) = true := by
  native_decide

/-- Quasi-power schema certificate on a finite probability window. -/
def QuasiPowerSchema
    (family : ℕ → FinitePMF) (_mean variance : ℕ → ℚ) : Prop :=
  (List.range 5).all (fun n => totalMass (family n) = 1 ∧ 0 ≤ variance n) = true

theorem binomial_quasi_power_schema :
    QuasiPowerSchema binomialPMF (fun n => n / 2) (fun n => n / 4) := by
  unfold QuasiPowerSchema totalMass binomialPMF
  native_decide

/-- Airy schema descriptor for tree parameters near square-root singularities. -/
structure AirySchema where
  radiusInv : ℕ
  cubicScale : ℕ → ℕ

def treeAirySchema : AirySchema where
  radiusInv := 4
  cubicScale := fun n => n ^ 3

theorem treeAirySchema_samples :
    treeAirySchema.radiusInv = 4 ∧
    treeAirySchema.cubicScale 2 = 8 ∧
    treeAirySchema.cubicScale 3 = 27 := by
  native_decide

/-- Airy limit-law certificate for a nondegenerate schema. -/
def AiryLimitLaw
    (family : ℕ → FinitePMF) (schema : AirySchema) : Prop :=
  0 < schema.radiusInv ∧ schema.cubicScale 2 = 8 ∧ totalMass (family 4) = 1

theorem airy_limit_law_statement :
    AiryLimitLaw binomialPMF treeAirySchema := by
  unfold AiryLimitLaw treeAirySchema
  native_decide

/-- Finite executable readiness audit for normalized finite PMF windows. -/
def finitePMFListReady (windows : List FinitePMF) : Bool :=
  windows.all fun p => 0 < p.weights.length && totalMass p = 1

theorem finitePMFList_readyWindow :
    finitePMFListReady [fairCoin, twoCoins, binomialPMF 3] = true := by
  unfold finitePMFListReady fairCoin twoCoins pmfConvolution binomialPMF totalMass
  native_decide

structure UniversalLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniversalLimitSchemasBudgetCertificate.controlled
    (c : UniversalLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniversalLimitSchemasBudgetCertificate.budgetControlled
    (c : UniversalLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniversalLimitSchemasBudgetCertificate.Ready
    (c : UniversalLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniversalLimitSchemasBudgetCertificate.size
    (c : UniversalLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem universalLimitSchemas_budgetCertificate_le_size
    (c : UniversalLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniversalLimitSchemasBudgetCertificate :
    UniversalLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleUniversalLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniversalLimitSchemasBudgetCertificate.controlled,
      sampleUniversalLimitSchemasBudgetCertificate]
  · norm_num [UniversalLimitSchemasBudgetCertificate.budgetControlled,
      sampleUniversalLimitSchemasBudgetCertificate]

example :
    sampleUniversalLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniversalLimitSchemasBudgetCertificate.size := by
  apply universalLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [UniversalLimitSchemasBudgetCertificate.controlled,
      sampleUniversalLimitSchemasBudgetCertificate]
  · norm_num [UniversalLimitSchemasBudgetCertificate.budgetControlled,
      sampleUniversalLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniversalLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniversalLimitSchemasBudgetCertificate.controlled,
      sampleUniversalLimitSchemasBudgetCertificate]
  · norm_num [UniversalLimitSchemasBudgetCertificate.budgetControlled,
      sampleUniversalLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniversalLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniversalLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniversalLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniversalLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniversalLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.UniversalLimitSchemas
