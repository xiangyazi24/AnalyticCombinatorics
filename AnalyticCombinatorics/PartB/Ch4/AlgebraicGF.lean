import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.AlgebraicGF


/-!
# Algebraic generating functions and Newton-Puiseux

Finite, computable coefficient checks for Chapter IV examples from analytic
combinatorics: algebraic ordinary generating functions, quadratic
discriminants, Catalan/Motzkin/Schroder families, and Narayana refinements.
-/

def convolution (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range n).foldl (fun total k => total + a k * a (n - 1 - k)) 0

def catalanTable : Fin 10 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]

def catalan (n : ℕ) : ℕ :=
  if h : n < 10 then catalanTable ⟨n, h⟩ else 0

def catalanQuadraticRhs (n : ℕ) : ℕ :=
  convolution catalan n

/-- Coefficient check for `C = 1 + z*C^2`, for `n = 1, ..., 9`. -/
theorem catalan_quadratic_GF_coefficients :
    ∀ n : Fin 9,
      catalan (n.val + 1) = catalanQuadraticRhs (n.val + 1) := by native_decide

def motzkinTable : Fin 9 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323]

def motzkin (n : ℕ) : ℕ :=
  if h : n < 9 then motzkinTable ⟨n, h⟩ else 0

def motzkinQuadraticRhs (n : ℕ) : ℕ :=
  motzkin (n - 1) +
    (List.range (n - 1)).foldl
      (fun total k => total + motzkin k * motzkin (n - 2 - k)) 0

/-- Coefficient check for `M = 1 + z*M + z^2*M^2`, for `n = 1, ..., 8`. -/
theorem motzkin_quadratic_GF_coefficients :
    ∀ n : Fin 8,
      motzkin (n.val + 1) = motzkinQuadraticRhs (n.val + 1) := by native_decide

def largeSchroderTable : Fin 7 → ℕ :=
  ![1, 2, 6, 22, 90, 394, 1806]

def largeSchroder (n : ℕ) : ℕ :=
  if h : n < 7 then largeSchroderTable ⟨n, h⟩ else 0

def schroderQuadraticRhs (n : ℕ) : ℕ :=
  largeSchroder (n - 1) + convolution largeSchroder n

/--
Coefficient check for `S = 1 + z*S + z*S^2`.
This normalization gives the large Schroder numbers.
-/
theorem schroder_quadratic_GF_coefficients :
    ∀ n : Fin 6,
      largeSchroder (n.val + 1) = schroderQuadraticRhs (n.val + 1) := by native_decide

def smallSchroderTable : Fin 8 → ℕ :=
  ![1, 1, 3, 11, 45, 197, 903, 4279]

def smallSchroder (n : ℕ) : ℕ :=
  if h : n < 8 then smallSchroderTable ⟨n, h⟩ else 0

/-- The requested small Schroder initial segment. -/
theorem small_schroder_values :
    smallSchroder 0 = 1 ∧
    smallSchroder 1 = 1 ∧
    smallSchroder 2 = 3 ∧
    smallSchroder 3 = 11 ∧
    smallSchroder 4 = 45 ∧
    smallSchroder 5 = 197 ∧
    smallSchroder 6 = 903 ∧
    smallSchroder 7 = 4279 := by native_decide

def smallSchroderAdjustedRhs (n : ℕ) : ℕ :=
  2 * convolution smallSchroder n - smallSchroder (n - 1)

/--
The small Schroder normalization adjusts the quadratic recurrence:
`s_n = 2 * sum_{k=0}^{n-1} s_k s_{n-1-k} - s_{n-1}`.
-/
theorem small_schroder_adjusted_convolution :
    ∀ n : Fin 6,
      smallSchroder (n.val + 1) = smallSchroderAdjustedRhs (n.val + 1) := by native_decide

def quadraticDiscriminant (a b c : ℚ) : ℚ :=
  b * b - 4 * a * c

def catalanDiscriminant (z : ℚ) : ℚ :=
  quadraticDiscriminant z (-1) 1

def quadraticSingularityCandidate (a b c : ℚ) : Prop :=
  quadraticDiscriminant a b c = 0

def quadraticSingularityCandidateBool (a b c : ℚ) : Bool :=
  quadraticDiscriminant a b c == 0

/--
For a quadratic algebraic generating function `P(z,y) = a(z)y^2 + b(z)y + c(z)`,
zeros of the discriminant mark singularity candidates.
-/
theorem catalan_discriminant_formula_samples :
    (catalanDiscriminant 0 == 1) = true ∧
    (catalanDiscriminant (1 / 4 : ℚ) == 0) = true ∧
    quadraticSingularityCandidateBool (1 / 4 : ℚ) (-1) 1 = true := by native_decide

/-- Rational check for the Catalan singularity of `y = 1 + z*y^2`. -/
theorem catalan_rational_singularity_check :
    (((1 : ℚ) - 4 * (1 / 4 : ℚ)) == 0) = true := by native_decide

def narayana (n k : ℕ) : ℕ :=
  if n = 0 ∨ k = 0 ∨ n < k then
    0
  else
    (Nat.choose n k * Nat.choose n (k - 1)) / n

theorem narayana_values :
    narayana 4 2 = 6 ∧
    narayana 5 2 = 10 ∧
    narayana 5 3 = 20 := by native_decide

/--
Ballot numbers for the valid parity case:
`B(n,k) = (k+1)/(n+1) * binom(n+1, (n-k)/2)`.
-/
def ballotNumber (n k : ℕ) : ℕ :=
  if k ≤ n ∧ (n - k) % 2 = 0 then
    ((k + 1) * Nat.choose (n + 1) ((n - k) / 2)) / (n + 1)
  else
    0

theorem ballot_number_formula_samples :
    ballotNumber 2 0 = 1 ∧
    ballotNumber 3 1 = 2 ∧
    ballotNumber 4 0 = 2 ∧
    ballotNumber 4 2 = 3 := by native_decide

def dyckPeaksTable : Fin 6 → Fin 6 → ℕ :=
  ![
    ![1, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0],
    ![1, 3, 1, 0, 0, 0],
    ![1, 6, 6, 1, 0, 0],
    ![1, 10, 20, 10, 1, 0],
    ![1, 15, 50, 50, 15, 1]
  ]

/--
For `1 <= n <= 6`, `1 <= k <= 6`, the table of Dyck paths of semilength `n`
with `k` peaks agrees with Narayana numbers `N(n,k)`.
-/
theorem dyck_paths_with_peaks_are_narayana :
    ∀ n : Fin 6, ∀ k : Fin 6,
      dyckPeaksTable n k = narayana (n.val + 1) (k.val + 1) := by native_decide

def narayanaRowSum (n : ℕ) : ℕ :=
  (List.range n).foldl (fun total k => total + narayana n (k + 1)) 0

/-- Narayana row sums give Catalan numbers, for `n = 1, ..., 6`. -/
theorem narayana_row_sum_catalan :
    ∀ n : Fin 6,
      narayanaRowSum (n.val + 1) = catalan (n.val + 1) := by native_decide



structure AlgebraicGFBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlgebraicGFBudgetCertificate.controlled
    (c : AlgebraicGFBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AlgebraicGFBudgetCertificate.budgetControlled
    (c : AlgebraicGFBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AlgebraicGFBudgetCertificate.Ready
    (c : AlgebraicGFBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlgebraicGFBudgetCertificate.size
    (c : AlgebraicGFBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem algebraicGF_budgetCertificate_le_size
    (c : AlgebraicGFBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAlgebraicGFBudgetCertificate :
    AlgebraicGFBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAlgebraicGFBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicGFBudgetCertificate.controlled,
      sampleAlgebraicGFBudgetCertificate]
  · norm_num [AlgebraicGFBudgetCertificate.budgetControlled,
      sampleAlgebraicGFBudgetCertificate]

example :
    sampleAlgebraicGFBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicGFBudgetCertificate.size := by
  apply algebraicGF_budgetCertificate_le_size
  constructor
  · norm_num [AlgebraicGFBudgetCertificate.controlled,
      sampleAlgebraicGFBudgetCertificate]
  · norm_num [AlgebraicGFBudgetCertificate.budgetControlled,
      sampleAlgebraicGFBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAlgebraicGFBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicGFBudgetCertificate.controlled,
      sampleAlgebraicGFBudgetCertificate]
  · norm_num [AlgebraicGFBudgetCertificate.budgetControlled,
      sampleAlgebraicGFBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlgebraicGFBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicGFBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AlgebraicGFBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAlgebraicGFBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAlgebraicGFBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.AlgebraicGF
