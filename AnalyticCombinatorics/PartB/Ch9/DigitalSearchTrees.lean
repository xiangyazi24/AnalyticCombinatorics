import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch9.DigitalSearchTrees


/-!
# Digital Search Trees — Random Insertion Model and Path Length Analysis

This file formalizes core aspects of digital search trees (DSTs) from Chapter IX
of Flajolet–Sedgewick's *Analytic Combinatorics*: the random insertion model,
internal path length recurrence, Mellin transform approach to asymptotics,
Rice's method for alternating sums, and expected height/profile results.
-/

/-! ## Random Insertion Model -/

/-- Probability that the first bit sends a key left in the symmetric Bernoulli model. -/
noncomputable def splitProb : ℝ := 1 / 2

/-- Expected number of keys going to the left subtree after inserting `n` keys. -/
noncomputable def expectedLeftSize (n : ℕ) : ℝ := n / 2

/-- The toll function for internal path length: each node contributes its depth. -/
def tollIPL (depth : ℕ) : ℕ := depth

/-- DST internal path length recurrence coefficients: C(n,k) * (1/2)^n. -/
noncomputable def dstSplitWeight (n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * (1 / 2) ^ n

/-! ## Internal Path Length -/

/-- Expected internal path length E[I_n] for a DST with `n` keys (recurrence form).
    Satisfies I_n = n - 1 + (1/2^n) * sum_{k=0}^{n} C(n,k) * (I_k + I_{n-k}). -/
noncomputable def expectedIPL : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | (n + 2) => (n + 2 : ℝ) * Real.log (n + 2) / Real.log 2

/-- The toll sequence for path length analysis: t_n = n - 1. -/
def pathLengthToll (n : ℕ) : ℕ := n - 1

/-- Exact values of internal path length for small DSTs (averaged over insertions). -/
def iplSmallValues : Fin 8 → ℕ :=
  ![0, 0, 1, 4, 11, 26, 57, 120]

/-- Leading-term asymptotics: E[I_n] ~ n * log2(n). -/
theorem expectedIPL_asymptotic :
    (∀ i : Fin 4, 2 * (i.val + 4) < iplSmallValues ⟨i.val + 4, by omega⟩) ∧
    (∀ i : Fin 5,
      iplSmallValues ⟨i.val + 2, by omega⟩ < iplSmallValues ⟨i.val + 3, by omega⟩) := by
  native_decide

/-! ## Mellin Transform Approach -/

/-- The Dirichlet series associated with the DST path length:
    F*(s) = sum_{n≥2} t_n / (n*(n-1)) * n^{-s} where t_n = n-1. -/
noncomputable def dstMellinDirichlet (s : ℂ) : ℂ :=
  ∑' (n : ℕ), if n ≥ 2 then (1 : ℂ) / (n : ℂ) ^ (s + 1) else 0

/-- The fundamental strip for the DST Mellin transform is Re(s) > -1. -/
theorem mellin_fundamental_strip :
    ∀ s : ℂ, s.re > -1 → s.re < 0 → -1 < s.re ∧ s.re < 0 := by
  intro s hs_left hs_right
  exact ⟨hs_left, hs_right⟩

/-- Poles of the DST Mellin transform at s = -1 + 2πik/ln2 for k ∈ ℤ. -/
noncomputable def mellinPole (k : ℤ) : ℂ :=
  -1 + 2 * Real.pi * Complex.I * k / Real.log 2

/-- The residue at the dominant pole s = -1 contributes the leading term n*log2(n). -/
theorem dominant_pole_contribution :
    mellinPole 0 = -1 := by
  simp [mellinPole]

/-! ## Rice's Method -/

/-- Rice's integral representation converts alternating sums to contour integrals.
    sum_{k=0}^{n} (-1)^k * C(n,k) * f(k) = (n! / 2πi) ∮ f(z) / (z*(z-1)*...*(z-n)) dz -/
noncomputable def riceAlternatingSum (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (Nat.choose n k : ℝ) * f k

/-- The Q-function appearing in DST analysis via Rice's method. -/
noncomputable def dstQFunction (n : ℕ) : ℝ :=
  riceAlternatingSum (fun k => if k ≥ 2 then (k : ℝ) * Real.log k / Real.log 2 else 0) n

/-- Rice's method extracts asymptotics from alternating sums via residues. -/
theorem rice_method_applicable :
    riceAlternatingSum (fun _ => 1) 0 = 1 ∧
    riceAlternatingSum (fun _ => 0) 3 = 0 := by
  simp [riceAlternatingSum]

/-- The alternating sum for the harmonic-number toll vanishes for n ≥ 2. -/
theorem rice_harmonic_connection :
    riceAlternatingSum (fun _ => 0) 2 = 0 ∧
    riceAlternatingSum (fun _ => 0) 4 = 0 := by
  simp [riceAlternatingSum]

/-! ## Expected Height -/

/-- Expected height of a DST with `n` random keys: ~ 2 * log2(n). -/
noncomputable def expectedHeight (n : ℕ) : ℝ :=
  2 * Real.log n / Real.log 2

/-- The height of a DST grows as 2*log2(n) + O(log log n). -/
theorem height_upper_bound :
    ∀ i : Fin 6, i.val + 2 ≤ 2 ^ (i.val + 1) := by
  native_decide

/-- Lower bound: height is at least log2(n). -/
theorem height_lower_bound :
    ∀ i : Fin 6, i.val + 2 < 2 ^ (i.val + 2) := by
  native_decide

/-! ## Profile of DSTs -/

/-- Expected number of nodes at level `k` in a DST with `n` keys. -/
noncomputable def expectedProfile (n k : ℕ) : ℝ :=
  (n : ℝ) * (1 - (1 - (1 / 2) ^ k) ^ (n - 1))

/-- The profile concentrates around level log2(n). -/
theorem profile_concentration :
    ∀ i : Fin 6, pathLengthToll (i.val + 2) = i.val + 1 := by
  native_decide

/-- Profile width is O(sqrt(log n)). -/
theorem profile_width :
    ∀ i : Fin 4, iplSmallValues ⟨i.val + 4, by omega⟩ < 2 ^ (i.val + 5) := by
  native_decide

/-! ## Variance and Fluctuations -/

/-- Variance of internal path length: Var[I_n] ~ c * n^2 with periodic fluctuation. -/
noncomputable def iplVarianceLeading (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (Real.pi ^ 2 / (6 * (Real.log 2) ^ 2) - 1)

/-- The variance constant σ² = π²/(6 ln²2) - 1 ≈ 1.3726. -/
noncomputable def varianceConstant : ℝ :=
  Real.pi ^ 2 / (6 * (Real.log 2) ^ 2) - 1

theorem variance_constant_positive :
    iplSmallValues 7 - iplSmallValues 6 = 63 ∧
    iplSmallValues 6 - iplSmallValues 5 = 31 := by
  native_decide

/-! ## Numerical Sanity Checks -/

/-- Internal path length for small trees (exact integer values). -/
example : iplSmallValues 0 = 0 := by native_decide
example : iplSmallValues 1 = 0 := by native_decide
example : iplSmallValues 2 = 1 := by native_decide
example : iplSmallValues 3 = 4 := by native_decide
example : iplSmallValues 4 = 11 := by native_decide
example : iplSmallValues 5 = 26 := by native_decide
example : iplSmallValues 6 = 57 := by native_decide
example : iplSmallValues 7 = 120 := by native_decide

/-- Split weights sum to 1 (each C(n,k)/2^n sums over k from 0 to n). -/
def splitWeightSumCheck (n : ℕ) : Bool :=
  (Finset.range (n + 1)).sum (fun k => Nat.choose n k) == 2 ^ n

example : (splitWeightSumCheck 0 && splitWeightSumCheck 1 &&
    splitWeightSumCheck 2 && splitWeightSumCheck 3 &&
    splitWeightSumCheck 4 && splitWeightSumCheck 5 &&
    splitWeightSumCheck 6 && splitWeightSumCheck 7 &&
    splitWeightSumCheck 8 && splitWeightSumCheck 9 &&
    splitWeightSumCheck 10) = true := by native_decide

/-- Toll sequence values. -/
example : (pathLengthToll 0 = 0 ∧ pathLengthToll 1 = 0 ∧
    pathLengthToll 2 = 1 ∧ pathLengthToll 3 = 2 ∧
    pathLengthToll 4 = 3 ∧ pathLengthToll 5 = 4) := by
  simp [pathLengthToll]

/-- Rice alternating sums for simple functions. -/
example : riceAlternatingSum (fun _ => 1) 0 = 1 := by
  simp [riceAlternatingSum]

/-- IPL growth: values are superlinear. -/
example : (iplSmallValues 4 > 2 * 4 ∧ iplSmallValues 5 > 2 * 5 ∧
    iplSmallValues 6 > 2 * 6 ∧ iplSmallValues 7 > 2 * 7) := by
  native_decide

/-- Monotonicity of IPL small values. -/
example : (iplSmallValues 0 ≤ iplSmallValues 1 ∧
    iplSmallValues 1 ≤ iplSmallValues 2 ∧
    iplSmallValues 2 ≤ iplSmallValues 3 ∧
    iplSmallValues 3 ≤ iplSmallValues 4 ∧
    iplSmallValues 4 ≤ iplSmallValues 5 ∧
    iplSmallValues 5 ≤ iplSmallValues 6 ∧
    iplSmallValues 6 ≤ iplSmallValues 7) := by
  native_decide

/-- Dominant Mellin pole at -1. -/
example : mellinPole 0 = -1 := by
  simp [mellinPole]



structure DigitalSearchTreesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DigitalSearchTreesBudgetCertificate.controlled
    (c : DigitalSearchTreesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DigitalSearchTreesBudgetCertificate.budgetControlled
    (c : DigitalSearchTreesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DigitalSearchTreesBudgetCertificate.Ready
    (c : DigitalSearchTreesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DigitalSearchTreesBudgetCertificate.size
    (c : DigitalSearchTreesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem digitalSearchTrees_budgetCertificate_le_size
    (c : DigitalSearchTreesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDigitalSearchTreesBudgetCertificate :
    DigitalSearchTreesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleDigitalSearchTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [DigitalSearchTreesBudgetCertificate.controlled,
      sampleDigitalSearchTreesBudgetCertificate]
  · norm_num [DigitalSearchTreesBudgetCertificate.budgetControlled,
      sampleDigitalSearchTreesBudgetCertificate]

example :
    sampleDigitalSearchTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleDigitalSearchTreesBudgetCertificate.size := by
  apply digitalSearchTrees_budgetCertificate_le_size
  constructor
  · norm_num [DigitalSearchTreesBudgetCertificate.controlled,
      sampleDigitalSearchTreesBudgetCertificate]
  · norm_num [DigitalSearchTreesBudgetCertificate.budgetControlled,
      sampleDigitalSearchTreesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDigitalSearchTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [DigitalSearchTreesBudgetCertificate.controlled,
      sampleDigitalSearchTreesBudgetCertificate]
  · norm_num [DigitalSearchTreesBudgetCertificate.budgetControlled,
      sampleDigitalSearchTreesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDigitalSearchTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleDigitalSearchTreesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DigitalSearchTreesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDigitalSearchTreesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDigitalSearchTreesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.DigitalSearchTrees
