/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI/VII — Algebraic singularities and finite coefficient checks.
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.Enumerative.Catalan
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Trees

set_option linter.style.nativeDecide false

open PowerSeries CombinatorialClass

/-! ## Algebraic functions as ordinary generating functions -/

/-- Evaluate a univariate polynomial in `z` as a rational power series. -/
noncomputable def polynomialAsPowerSeriesHom : Polynomial ℚ →+* PowerSeries ℚ :=
  (Polynomial.aeval (PowerSeries.X : PowerSeries ℚ)).toRingHom

/-- Evaluate a polynomial `P(z, y)` at `y = f(z)`, with polynomial coefficients in `z`. -/
noncomputable def evalAlgebraicPolynomial
    (P : Polynomial (Polynomial ℚ)) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  P.eval₂ polynomialAsPowerSeriesHom f

/-- An ordinary generating function is algebraic if it is annihilated by a
nonzero bivariate polynomial `P(z, y)` over `ℚ`. -/
def IsAlgebraicOGF (f : PowerSeries ℚ) : Prop :=
  ∃ P : Polynomial (Polynomial ℚ), P ≠ 0 ∧ evalAlgebraicPolynomial P f = 0

/-! ## Asymptotic predictions -/

/-- The Catalan square-root singularity predicts
`C_n ~ 4^n / (sqrt(pi) * n^(3/2))`. -/
noncomputable def catalanAsymptotic (n : ℕ) : ℝ :=
  (4 : ℝ) ^ n / (Real.sqrt Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2))

/-- The Motzkin square-root singularity predicts
`M_n ~ (3 * sqrt(3) / (2 * sqrt(pi))) * 3^n / n^(3/2)`. -/
noncomputable def motzkinAsymptotic (n : ℕ) : ℝ :=
  ((3 : ℝ) * Real.sqrt 3) / (2 * Real.sqrt Real.pi) *
    (3 : ℝ) ^ n / ((n : ℝ) ^ ((3 : ℝ) / 2))

/-! ## Catalan numbers and binary trees -/

/-- The binary-tree counts from Chapter I agree with Mathlib's Catalan numbers. -/
theorem algebraic_binaryTreeClass_count_eq_catalan (n : ℕ) :
    binaryTreeClass.count n = _root_.catalan n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [binaryTree_count_zero, _root_.catalan_zero]
      | succ n =>
          rw [binaryTree_count_recursion n, _root_.catalan_succ']
          apply Finset.sum_congr rfl
          intro p hp
          have hp1 : p.1 < n + 1 := by
            have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
            omega
          have hp2 : p.2 < n + 1 := by
            have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
            omega
          rw [ih p.1 hp1, ih p.2 hp2]

/-- Exact Catalan formula for the binary-tree class. -/
theorem algebraic_catalan_formula (n : ℕ) :
    binaryTreeClass.count n = (2 * n).choose n / (n + 1) := by
  rw [algebraic_binaryTreeClass_count_eq_catalan, _root_.catalan_eq_centralBinom_div]
  rfl

/-- General exponential upper bound `C_n < 4^n` for nonzero `n`. -/
theorem catalan_upper_4n (n : ℕ) (hn : 1 ≤ n) : binaryTreeClass.count n < 4 ^ n := by
  rw [algebraic_binaryTreeClass_count_eq_catalan, _root_.catalan_eq_centralBinom_div]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.centralBinom_lt_four_pow (by omega))

set_option linter.flexible false in
/-- The upper bound `C_n < 4^n`, verified directly for `n = 1, ..., 20`. -/
theorem catalan_upper_4n_1_20 :
    ∀ n ∈ Finset.Icc 1 20, binaryTreeClass.count n < 4 ^ n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> simp [algebraic_catalan_formula] <;> native_decide

set_option linter.flexible false in
/-- The scaled Catalan ratios `C_n (n+1) / 4^n` decrease on `n = 1, ..., 15`,
written as integer cross-multiplied inequalities. -/
theorem catalan_scaled_ratio_decreasing_1_15 :
    ∀ n ∈ Finset.Icc 1 14,
      binaryTreeClass.count (n + 1) * (n + 2) * 4 ^ n ≤
        binaryTreeClass.count n * (n + 1) * 4 ^ (n + 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> simp [algebraic_catalan_formula] <;> native_decide

set_option linter.flexible false in
/-- The scaled Catalan ratios are positive and at most `1`, represented without
rational division by `0 < C_n(n+1) ≤ 4^n`, for `n = 1, ..., 15`. -/
theorem catalan_scaled_ratio_bounded_1_15 :
    ∀ n ∈ Finset.Icc 1 15,
      0 < binaryTreeClass.count n * (n + 1) ∧
        binaryTreeClass.count n * (n + 1) ≤ 4 ^ n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> simp [algebraic_catalan_formula] <;> native_decide

/-- The requested lower bound `4^n / (4n) ≤ C_n` is already false at `n = 4`. -/
theorem catalan_lower_four_pow_div_four_mul_fails_at_4 :
    ¬ 4 ^ 4 / (4 * 4) ≤ binaryTreeClass.count 4 := by
  rw [algebraic_catalan_formula]
  native_decide

/-! ## Motzkin asymptotic finite checks -/

/-- Motzkin numbers in the convention `1, 1, 2, 4, 9, ...`. -/
def algebraicMotzkinNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
      algebraicMotzkinNumber (n + 1) +
        ∑ i : (Finset.range (n + 1) : Set ℕ),
          algebraicMotzkinNumber i.1 * algebraicMotzkinNumber (n - i.1)
termination_by n => n
decreasing_by
  all_goals simp_wf
  all_goals
    try
      have hi := Finset.mem_range.mp (show i.1 ∈ Finset.range (n + 1) from i.2)
    omega

/-- `M_n < 3^n` for `n = 1, ..., 15`. -/
theorem motzkin_lt_three_pow_1_15 :
    ∀ n ∈ Finset.Icc 1 15, algebraicMotzkinNumber n < 3 ^ n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

/-- The requested lower bound `2^n < M_n` is false at `n = 3`. -/
theorem two_pow_lt_motzkin_fails_at_3 :
    ¬ 2 ^ 3 < algebraicMotzkinNumber 3 := by
  native_decide

/-- `2^n < M_n` for `n = 8, ..., 15`, where this finite lower check becomes true. -/
theorem two_pow_lt_motzkin_8_15 :
    ∀ n ∈ Finset.Icc 8 15, 2 ^ n < algebraicMotzkinNumber n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide
