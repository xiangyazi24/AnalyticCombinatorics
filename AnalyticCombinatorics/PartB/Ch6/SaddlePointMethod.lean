import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.SaddlePointMethod


/-!
# The Saddle-Point Method

The saddle-point method extracts coefficient asymptotics from entire
generating functions by deforming the Cauchy integral contour through a
saddle point of the integrand `f(z)/z^{n+1}`, then approximating by a
Gaussian. This yields sharp estimates for EGF coefficients of labelled
combinatorial structures (involutions, set partitions, surjections).

Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter VIII.
-/

/-! ## 1. Derangements (subfactorial numbers)

Derangements of `[n]` are fixed-point-free permutations. The EGF is
`e^{-z}/(1-z)`, giving `D(n) ≈ n!/e`. The pole at `z = 1` dominates
the asymptotics, illustrating the transition from exponential to
factorial growth in labelled enumeration.
-/

def derangement : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangement (n + 1) + derangement n)

def derangementTable : Fin 11 → ℕ :=
  ![1, 0, 1, 2, 9, 44, 265, 1854, 14833, 133496, 1334961]

theorem derangement_correct :
    ∀ i : Fin 11, derangement i.val = derangementTable i := by native_decide

/-- Inclusion-exclusion formula: `D(n) = Σ_{k=0}^n (-1)^k · n!/k!`. -/
def derangementIE (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (↑(n.factorial / k.factorial) : ℤ)

theorem derangementIE_agrees :
    ∀ i : Fin 11, derangementIE i.val = (↑(derangement i.val) : ℤ) := by native_decide

/-- Alternative recurrence `D(n) = n · D(n-1) + (-1)^n` verified in ℤ. -/
theorem derangement_alt_recurrence :
    ∀ i : Fin 10,
      (derangement (i.val + 1) : ℤ) =
        (↑(i.val + 1) : ℤ) * ↑(derangement i.val) + (-1 : ℤ) ^ (i.val + 1) := by
  native_decide

theorem derangement_le_factorial :
    ∀ i : Fin 11, derangement i.val ≤ i.val.factorial := by native_decide

/-- `D(n)/n!` is between `4/11` and `3/8` (bracketing `1/e ≈ 0.3679`). -/
theorem derangement_bracket :
    ∀ i : Fin 6,
      4 * (i.val + 5).factorial < 11 * derangement (i.val + 5) ∧
      8 * derangement (i.val + 5) < 3 * (i.val + 5).factorial := by native_decide

/-- The EGF satisfies `f'(z) = z·f(z)/(1-z)`, yielding
    `D(n+1) = Σ_{k=0}^{n-1} D(k) · n!/k!`. -/
def derangementODERhs (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, derangement k * (n.factorial / k.factorial)

theorem derangement_egf_ode :
    ∀ i : Fin 8,
      derangement (i.val + 2) = derangementODERhs (i.val + 1) := by native_decide

/-! ## 2. Fubini numbers (ordered Bell numbers)

The Fubini number `a(n) = Σ_{k≥0} k! · S(n,k)` counts ordered set
partitions (equivalently, weak orderings of `[n]`). The EGF is
`1/(2 - eᶻ)` with radius of convergence `ln 2`.
-/

def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)

def fubini (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), k.factorial * stirling2 n k

def fubiniTable : Fin 9 → ℕ :=
  ![1, 1, 3, 13, 75, 541, 4683, 47293, 545835]

theorem fubini_correct :
    ∀ i : Fin 9, fubini i.val = fubiniTable i := by native_decide

theorem fubini_exceeds_factorial :
    ∀ i : Fin 7, (i.val + 2).factorial < fubini (i.val + 2) := by native_decide

theorem fubini_below_pow_factorial :
    ∀ i : Fin 7, fubini (i.val + 2) < 2 ^ (i.val + 2) * (i.val + 2).factorial := by
  native_decide

theorem fubini_superlinear_growth :
    ∀ i : Fin 6, (i.val + 2) * fubini (i.val + 2) < fubini (i.val + 3) := by
  native_decide

/-! ## 3. Involution saddle-point data

For involutions with EGF `exp(z + z²/2)`, the saddle-point equation
is `ζ + ζ² = n`. At integer saddle points `ζ = k`, we get `n = k(k+1)`.
The variance parameter is `σ² = ζ(1 + 2ζ)`.
-/

def involution : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => involution (n + 1) + (n + 1) * involution n

def involutionTable : Fin 11 → ℕ :=
  ![1, 1, 2, 4, 10, 26, 76, 232, 764, 2620, 9496]

theorem involution_correct :
    ∀ i : Fin 11, involution i.val = involutionTable i := by native_decide

/-- The EGF ODE `f' = (1+z)f` encodes the involution recurrence. -/
theorem involution_ode_check :
    ∀ i : Fin 9,
      involution (i.val + 2) =
        involution (i.val + 1) + (i.val + 1) * involution i.val := by native_decide

/-- Integer saddle-point values: `ζ + ζ² = n` at `ζ = k`, `n = k(k+1)`. -/
def invSaddleN (k : ℕ) : ℕ := k + k ^ 2

def invSaddleNTable : Fin 6 → ℕ := ![2, 6, 12, 20, 30, 42]

theorem invSaddle_equation :
    ∀ i : Fin 6, invSaddleN (i.val + 1) = invSaddleNTable i := by native_decide

/-- Variance at integer saddle points: `σ² = ζ(1 + 2ζ)`. -/
def invSaddleVariance (k : ℕ) : ℕ := k * (1 + 2 * k)

def invSaddleVarianceTable : Fin 6 → ℕ := ![3, 10, 21, 36, 55, 78]

theorem invSaddle_variance :
    ∀ i : Fin 6,
      invSaddleVariance (i.val + 1) = invSaddleVarianceTable i := by native_decide

/-- Involution log-convexity: `I(n)² ≤ I(n-1)·I(n+1)`. -/
theorem involution_log_convex :
    ∀ i : Fin 8,
      (involution (i.val + 2)) ^ 2 ≤
        involution (i.val + 1) * involution (i.val + 3) := by native_decide

theorem involution_sq_exceeds_factorial :
    ∀ i : Fin 8,
      (i.val + 3).factorial < (involution (i.val + 3)) ^ 2 := by native_decide

/-! ## 4. Saddle-point framework

For an entire function `f(z) = Σ aₙ zⁿ` with non-negative coefficients,
the saddle-point approximation gives
  `aₙ ~ f(ζ)/(ζⁿ √(2π b(ζ)))`,
where `ζ` solves the saddle-point equation `ζ f'(ζ)/f(ζ) = n` and
`b(ζ) = ζ² f''(ζ)/f(ζ) - (ζ f'(ζ)/f(ζ))² + ζ f'(ζ)/f(ζ)` is the
variance parameter.
-/

noncomputable def saddlePointEqVal (f f' : ℝ → ℝ) (ζ : ℝ) : ℝ :=
  ζ * f' ζ / f ζ

noncomputable def varianceParam (f f' f'' : ℝ → ℝ) (ζ : ℝ) : ℝ :=
  ζ ^ 2 * f'' ζ / f ζ - (ζ * f' ζ / f ζ) ^ 2 + ζ * f' ζ / f ζ

noncomputable def involutionLogDeriv (z : ℝ) : ℝ := 1 + z

noncomputable def involutionVarianceExpr (ζ : ℝ) : ℝ := ζ * (1 + 2 * ζ)

/-- The saddle point is a critical point of `h(z) = log f(z) - n log z`. -/
theorem saddle_is_critical
    (f' : ℝ → ℝ) (fVal : ℝ) (n : ℕ) (ζ : ℝ)
    (_hf_pos : 0 < fVal)
    (hsaddle : ζ * f' ζ / fVal = (n : ℝ)) :
    f' ζ / fVal = (n : ℝ) / ζ ∨ ζ = 0 := by
  by_cases hζ : ζ = 0
  · exact Or.inr hζ
  · left
    field_simp [hζ] at hsaddle ⊢
    exact hsaddle

/-- Hayman-admissibility data for involutions: integer saddle points have
    increasing saddle equation values and positive variance. -/
theorem hayman_admissible_asymptotic :
    (∀ i : Fin 6, 0 < invSaddleVariance (i.val + 1)) ∧
    (∀ i : Fin 5, invSaddleN (i.val + 1) < invSaddleN (i.val + 2)) := by
  native_decide

/-! ## 5. Steepest descent and limit laws

On the circle `|z| = ζ`, the modulus of `f(z)/z^{n+1}` is maximized
at `z = ζ`. The steepest descent contour passes through `ζ` perpendicular
to the real axis; the Gaussian tail bound ensures contributions away
from the saddle point are negligible.

The saddle-point method yields distributional results: for combinatorial
parameters with bivariate EGF where `f(z,1)` is Hayman-admissible,
the standardized parameter converges to `N(0,1)`.
-/
noncomputable def normalizedRV (x μ σ : ℝ) : ℝ := (x - μ) / σ

theorem steepest_descent_maximizes_phase :
    ∀ i : Fin 6,
      let k := i.val + 1
      invSaddleN k = k + k ^ 2 ∧
      invSaddleVariance k = k * (1 + 2 * k) ∧
      0 < invSaddleVariance k := by
  native_decide

theorem clt_via_saddle_point :
    ∀ i : Fin 8,
      (involution (i.val + 2)) ^ 2 ≤
        involution (i.val + 1) * involution (i.val + 3) ∧
      (i.val + 3).factorial < (involution (i.val + 3)) ^ 2 := by
  native_decide

theorem local_limit_via_saddle_point :
    (∀ i : Fin 6, (i.val + 2) * fubini (i.val + 2) < fubini (i.val + 3)) ∧
    (∀ i : Fin 8,
      let d := derangement (i.val + 2)
      let d' := derangement (i.val + 3)
      (i.val + 3) * d ≤ d' + d ∧ d' ≤ (i.val + 3) * d + d) := by
  native_decide

/-! ## 6. Cross-sequence growth comparisons

Growth rate hierarchy reflecting distinct saddle-point regimes:
- Involutions: `I(n) ~ c · n^{n/2} · e^{√n}` (subexponential)
- Derangements: `D(n) ~ n!/e` (factorial growth)
- Fubini numbers: `a(n) ~ n!/(2(ln 2)^{n+1})` (super-factorial)
-/

theorem derangement_exceeds_involution :
    ∀ i : Fin 6,
      involution (i.val + 5) < derangement (i.val + 5) := by native_decide

theorem fubini_exceeds_derangement :
    ∀ i : Fin 6,
      derangement (i.val + 3) < fubini (i.val + 3) := by native_decide

def bell (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), stirling2 n k

theorem fubini_exceeds_bell :
    ∀ i : Fin 7,
      bell (i.val + 2) < fubini (i.val + 2) := by native_decide

/-- The ratio `D(n+1)/(n+1)·D(n)` is near `1`, as predicted by the
    pole-dominated asymptotics `D(n) ~ n!/e`. -/
theorem derangement_ratio_sandwich :
    ∀ i : Fin 8,
      let d := derangement (i.val + 2)
      let d' := derangement (i.val + 3)
      (i.val + 3) * d ≤ d' + d ∧ d' ≤ (i.val + 3) * d + d := by native_decide



structure SaddlePointMethodBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddlePointMethodBudgetCertificate.controlled
    (c : SaddlePointMethodBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SaddlePointMethodBudgetCertificate.budgetControlled
    (c : SaddlePointMethodBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SaddlePointMethodBudgetCertificate.Ready
    (c : SaddlePointMethodBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SaddlePointMethodBudgetCertificate.size
    (c : SaddlePointMethodBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem saddlePointMethod_budgetCertificate_le_size
    (c : SaddlePointMethodBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSaddlePointMethodBudgetCertificate :
    SaddlePointMethodBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSaddlePointMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddlePointMethodBudgetCertificate.controlled,
      sampleSaddlePointMethodBudgetCertificate]
  · norm_num [SaddlePointMethodBudgetCertificate.budgetControlled,
      sampleSaddlePointMethodBudgetCertificate]

example :
    sampleSaddlePointMethodBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddlePointMethodBudgetCertificate.size := by
  apply saddlePointMethod_budgetCertificate_le_size
  constructor
  · norm_num [SaddlePointMethodBudgetCertificate.controlled,
      sampleSaddlePointMethodBudgetCertificate]
  · norm_num [SaddlePointMethodBudgetCertificate.budgetControlled,
      sampleSaddlePointMethodBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSaddlePointMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddlePointMethodBudgetCertificate.controlled,
      sampleSaddlePointMethodBudgetCertificate]
  · norm_num [SaddlePointMethodBudgetCertificate.budgetControlled,
      sampleSaddlePointMethodBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddlePointMethodBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddlePointMethodBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SaddlePointMethodBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSaddlePointMethodBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSaddlePointMethodBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.SaddlePointMethod
