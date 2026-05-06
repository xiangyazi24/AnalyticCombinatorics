import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Growth Scales

Finite models for polynomial, exponential, factorial, and stretched
exponential scales.
-/

namespace AnalyticCombinatorics.Asymptotics.GrowthScales

def polynomialScale (d n : ℕ) : ℕ := n ^ d

def exponentialScale (ρinv n : ℕ) : ℕ := ρinv ^ n

def factorialScale (n : ℕ) : ℕ := Nat.factorial n

def stretchedScaleModel (base n : ℕ) : ℕ := base ^ (n * n)

theorem polynomialScale_zero_degree (n : ℕ) :
    polynomialScale 0 n = 1 := by
  simp [polynomialScale]

theorem polynomialScale_one_degree (n : ℕ) :
    polynomialScale 1 n = n := by
  simp [polynomialScale]

theorem exponentialScale_zero_index (ρinv : ℕ) :
    exponentialScale ρinv 0 = 1 := by
  simp [exponentialScale]

theorem exponentialScale_one_base (n : ℕ) :
    exponentialScale 1 n = 1 := by
  simp [exponentialScale]

theorem factorialScale_succ (n : ℕ) :
    factorialScale (n + 1) = (n + 1) * factorialScale n := by
  simp [factorialScale, Nat.factorial_succ]

theorem polynomial_samples :
    polynomialScale 3 0 = 0 ∧
    polynomialScale 3 1 = 1 ∧
    polynomialScale 3 2 = 8 ∧
    polynomialScale 3 3 = 27 := by
  native_decide

theorem exponential_samples :
    exponentialScale 3 0 = 1 ∧
    exponentialScale 3 1 = 3 ∧
    exponentialScale 3 2 = 9 ∧
    exponentialScale 3 3 = 27 := by
  native_decide

theorem factorial_samples :
    factorialScale 0 = 1 ∧
    factorialScale 1 = 1 ∧
    factorialScale 2 = 2 ∧
    factorialScale 3 = 6 ∧
    factorialScale 4 = 24 ∧
    factorialScale 5 = 120 := by
  native_decide

/-- Finite hierarchy check: polynomial is below exponential on a sampled tail. -/
def polyBelowExpCheck (d base n0 N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n < n0 then true else polynomialScale d n ≤ exponentialScale base n

theorem quadratic_below_two_pow_4_20 :
    polyBelowExpCheck 2 2 4 20 = true := by
  native_decide

theorem cubic_below_three_pow_3_15 :
    polyBelowExpCheck 3 3 3 15 = true := by
  native_decide

/-- Finite hierarchy check: exponential is below factorial on a sampled tail. -/
def expBelowFactorialCheck (base n0 N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n < n0 then true else exponentialScale base n ≤ factorialScale n

theorem two_pow_below_factorial_4_12 :
    expBelowFactorialCheck 2 4 12 = true := by
  native_decide

theorem three_pow_below_factorial_7_14 :
    expBelowFactorialCheck 3 7 14 = true := by
  native_decide

/-- Logarithmic scale model using integer bit-length. -/
def logTwoScale : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.log2 (n + 1)

theorem logTwoScale_zero :
    logTwoScale 0 = 0 := rfl

theorem logTwoScale_succ (n : ℕ) :
    logTwoScale (n + 1) = Nat.log2 (n + 1) := rfl

theorem logTwoScale_samples :
    logTwoScale 1 = 0 ∧
    logTwoScale 2 = 1 ∧
    logTwoScale 3 = 1 ∧
    logTwoScale 4 = 2 ∧
    logTwoScale 8 = 3 ∧
    logTwoScale 16 = 4 := by
  native_decide

/-- Finite positivity certificate for a sampled asymptotic scale family. -/
def CompleteAsymptoticScale
    (scale : ℕ → ℕ → ℕ) (K N : ℕ) : Prop :=
  (List.range (K + 1)).all (fun k =>
    (List.range (N + 1)).all fun n => 0 < scale k (n + 1)) = true

theorem polynomial_exponential_factorial_scale_statement :
    CompleteAsymptoticScale
      (fun k n => polynomialScale k n + exponentialScale (k + 2) n + factorialScale n) 4 6 := by
  unfold CompleteAsymptoticScale polynomialScale exponentialScale factorialScale
  native_decide

structure GrowthScaleCertificate where
  polynomialDegree : ℕ
  exponentialBase : ℕ
  sampleTail : ℕ
  hierarchyBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GrowthScaleCertificate.tailControlled
    (c : GrowthScaleCertificate) : Prop :=
  c.sampleTail ≤ c.polynomialDegree + c.exponentialBase + c.slack

def GrowthScaleCertificate.hierarchyControlled
    (c : GrowthScaleCertificate) : Prop :=
  c.hierarchyBudget ≤
    c.polynomialDegree + c.exponentialBase + c.sampleTail + c.slack

def growthScaleCertificateReady
    (c : GrowthScaleCertificate) : Prop :=
  0 < c.exponentialBase ∧ c.tailControlled ∧ c.hierarchyControlled

def GrowthScaleCertificate.size (c : GrowthScaleCertificate) : ℕ :=
  c.polynomialDegree + c.exponentialBase + c.sampleTail + c.slack

theorem growthScale_hierarchyBudget_le_size
    {c : GrowthScaleCertificate}
    (h : growthScaleCertificateReady c) :
    c.hierarchyBudget ≤ c.size := by
  rcases h with ⟨_, _, hhierarchy⟩
  exact hhierarchy

def sampleGrowthScaleCertificate : GrowthScaleCertificate :=
  { polynomialDegree := 3, exponentialBase := 2, sampleTail := 4,
    hierarchyBudget := 9, slack := 0 }

example : growthScaleCertificateReady sampleGrowthScaleCertificate := by
  norm_num [growthScaleCertificateReady,
    GrowthScaleCertificate.tailControlled,
    GrowthScaleCertificate.hierarchyControlled,
    sampleGrowthScaleCertificate]

example :
    sampleGrowthScaleCertificate.hierarchyBudget ≤
      sampleGrowthScaleCertificate.size := by
  norm_num [GrowthScaleCertificate.size, sampleGrowthScaleCertificate]

/-- Finite executable readiness audit for growth-scale certificates. -/
def growthScaleCertificateListReady
    (certs : List GrowthScaleCertificate) : Bool :=
  certs.all fun c =>
    0 < c.exponentialBase &&
      c.sampleTail ≤ c.polynomialDegree + c.exponentialBase + c.slack &&
        c.hierarchyBudget ≤
          c.polynomialDegree + c.exponentialBase + c.sampleTail + c.slack

theorem growthScaleCertificateList_readyWindow :
    growthScaleCertificateListReady
      [{ polynomialDegree := 2, exponentialBase := 2, sampleTail := 4,
         hierarchyBudget := 8, slack := 0 },
       { polynomialDegree := 3, exponentialBase := 2, sampleTail := 4,
         hierarchyBudget := 9, slack := 0 }] = true := by
  unfold growthScaleCertificateListReady
  native_decide

/-- A refinement certificate with the growth-hierarchy budget separated from size. -/
structure GrowthScaleRefinementCertificate where
  polynomialDegree : ℕ
  exponentialBase : ℕ
  sampleTail : ℕ
  hierarchyBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GrowthScaleRefinementCertificate.hierarchyControlled
    (cert : GrowthScaleRefinementCertificate) : Prop :=
  0 < cert.exponentialBase ∧
    cert.sampleTail ≤ cert.polynomialDegree + cert.exponentialBase + cert.slack ∧
      cert.hierarchyBudgetWindow ≤
        cert.polynomialDegree + cert.exponentialBase + cert.sampleTail + cert.slack

def GrowthScaleRefinementCertificate.budgetControlled
    (cert : GrowthScaleRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.polynomialDegree + cert.exponentialBase + cert.sampleTail +
      cert.hierarchyBudgetWindow + cert.slack

def growthScaleRefinementReady
    (cert : GrowthScaleRefinementCertificate) : Prop :=
  cert.hierarchyControlled ∧ cert.budgetControlled

def GrowthScaleRefinementCertificate.size
    (cert : GrowthScaleRefinementCertificate) : ℕ :=
  cert.polynomialDegree + cert.exponentialBase + cert.sampleTail +
    cert.hierarchyBudgetWindow + cert.slack

theorem growthScale_certificateBudgetWindow_le_size
    (cert : GrowthScaleRefinementCertificate)
    (h : growthScaleRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGrowthScaleRefinementCertificate :
    GrowthScaleRefinementCertificate :=
  { polynomialDegree := 3, exponentialBase := 2, sampleTail := 4,
    hierarchyBudgetWindow := 9, certificateBudgetWindow := 18, slack := 0 }

example :
    growthScaleRefinementReady sampleGrowthScaleRefinementCertificate := by
  norm_num [growthScaleRefinementReady,
    GrowthScaleRefinementCertificate.hierarchyControlled,
    GrowthScaleRefinementCertificate.budgetControlled,
    sampleGrowthScaleRefinementCertificate]

example :
    sampleGrowthScaleRefinementCertificate.certificateBudgetWindow ≤
      sampleGrowthScaleRefinementCertificate.size := by
  apply growthScale_certificateBudgetWindow_le_size
  norm_num [growthScaleRefinementReady,
    GrowthScaleRefinementCertificate.hierarchyControlled,
    GrowthScaleRefinementCertificate.budgetControlled,
    sampleGrowthScaleRefinementCertificate]


structure GrowthScalesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GrowthScalesBudgetCertificate.controlled
    (c : GrowthScalesBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def GrowthScalesBudgetCertificate.budgetControlled
    (c : GrowthScalesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def GrowthScalesBudgetCertificate.Ready
    (c : GrowthScalesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GrowthScalesBudgetCertificate.size
    (c : GrowthScalesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem growthScales_budgetCertificate_le_size
    (c : GrowthScalesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGrowthScalesBudgetCertificate :
    GrowthScalesBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleGrowthScalesBudgetCertificate.Ready := by
  constructor
  · norm_num [GrowthScalesBudgetCertificate.controlled,
      sampleGrowthScalesBudgetCertificate]
  · norm_num [GrowthScalesBudgetCertificate.budgetControlled,
      sampleGrowthScalesBudgetCertificate]

example :
    sampleGrowthScalesBudgetCertificate.certificateBudgetWindow ≤
      sampleGrowthScalesBudgetCertificate.size := by
  apply growthScales_budgetCertificate_le_size
  constructor
  · norm_num [GrowthScalesBudgetCertificate.controlled,
      sampleGrowthScalesBudgetCertificate]
  · norm_num [GrowthScalesBudgetCertificate.budgetControlled,
      sampleGrowthScalesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleGrowthScalesBudgetCertificate.Ready := by
  constructor
  · norm_num [GrowthScalesBudgetCertificate.controlled,
      sampleGrowthScalesBudgetCertificate]
  · norm_num [GrowthScalesBudgetCertificate.budgetControlled,
      sampleGrowthScalesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGrowthScalesBudgetCertificate.certificateBudgetWindow ≤
      sampleGrowthScalesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List GrowthScalesBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGrowthScalesBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleGrowthScalesBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.GrowthScales
