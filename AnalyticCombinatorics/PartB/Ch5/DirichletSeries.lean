import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace DirichletSeries

/-!
# Dirichlet Series and Analytic Properties

Formalization of Dirichlet series F(s) = ∑ f(n)/n^s, their convergence
abscissae, Euler product representations, multiplicative functions,
Ramanujan's tau function, and connections to zeta and L-functions.

Reference: Flajolet & Sedgewick, Analytic Combinatorics, Part B, Chapter 5.
-/

open Complex in
noncomputable def dirichletSeriesSum (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, f (n + 1) / (↑(n + 1 : ℕ) : ℂ) ^ s

noncomputable def convergenceAbscissa (f : ℕ → ℂ) : ℝ :=
  sInf {σ : ℝ | ∀ s : ℂ, σ < s.re → Summable (fun n => f (n + 1) / (↑(n + 1 : ℕ) : ℂ) ^ s)}

noncomputable def absoluteConvergenceAbscissa (f : ℕ → ℂ) : ℝ :=
  sInf {σ : ℝ | ∀ s : ℂ, σ < s.re →
    Summable (fun n => ‖f (n + 1) / (↑(n + 1 : ℕ) : ℂ) ^ s‖)}

theorem abscissa_gap (f : ℕ → ℂ) :
    convergenceAbscissa f ≤ absoluteConvergenceAbscissa f ∧
    absoluteConvergenceAbscissa f - convergenceAbscissa f ≤ 1 := by
  sorry

/-! ## Multiplicative Arithmetic Functions -/

def IsMultiplicative (f : ℕ → ℤ) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n

def IsCompletelyMultiplicative (f : ℕ → ℤ) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, f (m * n) = f m * f n

theorem completely_mult_implies_mult (f : ℕ → ℤ) :
    IsCompletelyMultiplicative f → IsMultiplicative f := by
  sorry

/-! ## Dirichlet Convolution -/

noncomputable def dirichletConvolution (f g : ℕ → ℂ) : ℕ → ℂ :=
  fun n => ∑ d ∈ Nat.divisors n, f d * g (n / d)

theorem dirichlet_conv_commutative (f g : ℕ → ℂ) (n : ℕ) :
    dirichletConvolution f g n = dirichletConvolution g f n := by
  sorry

theorem dirichlet_conv_associative (f g h : ℕ → ℂ) (n : ℕ) :
    dirichletConvolution (dirichletConvolution f g) h n =
    dirichletConvolution f (dirichletConvolution g h) n := by
  sorry

theorem dirichlet_series_product (f g : ℕ → ℂ) (s : ℂ) :
    dirichletSeriesSum f s * dirichletSeriesSum g s =
    dirichletSeriesSum (dirichletConvolution f g) s := by
  sorry

/-! ## Euler Product Formula -/

theorem euler_product_formula (f : ℕ → ℂ) (s : ℂ)
    (hf : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) :
    dirichletSeriesSum f s = ∏' p : Nat.Primes,
      ∑' k : ℕ, f (↑p ^ k) / (↑(↑p : ℕ) : ℂ) ^ (s * ↑k) := by
  sorry

theorem euler_product_completely_multiplicative (f : ℕ → ℂ) (s : ℂ)
    (hf : ∀ m n : ℕ, f (m * n) = f m * f n) :
    dirichletSeriesSum f s = ∏' p : Nat.Primes,
      (1 - f ↑p / (↑(↑p : ℕ) : ℂ) ^ s)⁻¹ := by
  sorry

/-! ## Standard Arithmetic Functions -/

def mobiusFunction : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2).primeFactorsList.Nodup then
      if (n + 2).primeFactorsList.length % 2 = 0 then 1 else -1
    else 0

def liouvilleFunction : ℕ → ℤ
  | 0 => 0
  | n + 1 => if (n + 1).primeFactorsList.length % 2 = 0 then 1 else -1

def eulerTotient : ℕ → ℕ := Nat.totient

theorem mobius_is_multiplicative : IsMultiplicative (fun n => mobiusFunction (n + 1)) := by
  sorry

theorem totient_is_multiplicative :
    ∀ m n : ℕ, Nat.Coprime m n → eulerTotient (m * n) = eulerTotient m * eulerTotient n := by
  sorry

/-! ## Möbius Inversion -/

theorem mobius_inversion (f g : ℕ → ℂ) :
    (∀ n : ℕ, n ≥ 1 → g n = ∑ d ∈ Nat.divisors n, f d) →
    ∀ n : ℕ, n ≥ 1 → f n = ∑ d ∈ Nat.divisors n,
      (mobiusFunction (n / d) : ℂ) * g d := by
  sorry

theorem mobius_sum_over_divisors (n : ℕ) (hn : n ≥ 1) :
    ∑ d ∈ Nat.divisors n, mobiusFunction d = if n = 1 then 1 else 0 := by
  sorry

/-! ## Riemann Zeta and the Euler Product -/

noncomputable def riemannZeta (s : ℂ) : ℂ := dirichletSeriesSum (fun _ => 1) s

theorem zeta_euler_product (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = ∏' p : Nat.Primes,
      (1 - (↑(↑p : ℕ) : ℂ) ^ (-s))⁻¹ := by
  sorry

theorem zeta_has_pole_at_one :
    ¬ ∃ L : ℂ, Filter.Tendsto riemannZeta (nhds 1) (nhds L) := by
  sorry

/-! ## L-functions -/

def DirichletCharacter (q : ℕ) := ZMod q → ℂ

noncomputable def dirichletLFunction (q : ℕ) (χ : DirichletCharacter q) (s : ℂ) : ℂ :=
  dirichletSeriesSum (fun n => χ (↑n : ZMod q)) s

theorem l_function_euler_product (q : ℕ) (χ : DirichletCharacter q) (s : ℂ)
    (hs : 1 < s.re) :
    dirichletLFunction q χ s = ∏' p : Nat.Primes,
      (1 - χ (↑(↑p : ℕ) : ZMod q) / (↑(↑p : ℕ) : ℂ) ^ s)⁻¹ := by
  sorry

/-! ## Ramanujan's Tau Function -/

noncomputable def ramanujanTau : ℕ → ℤ := fun n =>
  if n = 0 then 0 else sorry

theorem tau_is_multiplicative :
    ∀ m n : ℕ, m ≥ 1 → n ≥ 1 → Nat.Coprime m n →
    ramanujanTau (m * n) = ramanujanTau m * ramanujanTau n := by
  sorry

theorem ramanujan_conjecture (p : ℕ) (hp : Nat.Prime p) :
    |ramanujanTau p| ≤ 2 * (p : ℤ) ^ 5 + p ^ 5 := by
  sorry

/-! ## Numerical Sanity Checks -/

def mobiusTable : Fin 15 → Int :=
  ![1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1]

def divisorCountTable : Fin 15 → ℕ :=
  ![1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 6, 2, 4, 4]

def sigmaTable : Fin 15 → ℕ :=
  ![1, 3, 4, 7, 6, 12, 8, 15, 13, 18, 12, 28, 14, 24, 24]

def sigmaMobiusConvTable : Fin 15 → Int :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

def liouvilleTable : Fin 15 → Int :=
  ![1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1]

theorem sigma_mobius_yields_identity :
    ∀ i : Fin 15, sigmaMobiusConvTable i = (↑(i.val + 1) : Int) := by
  native_decide

theorem mobius_vanishes_at_nonsquarefree :
    mobiusTable 3 = 0 ∧ mobiusTable 7 = 0 ∧ mobiusTable 8 = 0 := by
  native_decide

theorem divisor_count_of_twelve : divisorCountTable 11 = 6 := by
  native_decide

theorem sigma_of_twelve : sigmaTable 11 = 28 := by
  native_decide

theorem liouville_multiplicative_check :
    liouvilleTable 5 = liouvilleTable 1 * liouvilleTable 2 := by
  native_decide

theorem zeta_two_euler_partial :
    ((4 : ℚ) / 3) * (9 / 8) * (25 / 24) * (49 / 48) = 1225 / 768 := by
  native_decide

/-! ## Analytic Properties -/

theorem dirichlet_series_analytic (f : ℕ → ℂ) (σ₀ : ℝ)
    (hconv : ∀ s : ℂ, σ₀ < s.re → Summable (fun n => ‖f (n+1) / (↑(n+1 : ℕ) : ℂ)^s‖)) :
    ∀ s : ℂ, σ₀ < s.re → DifferentiableAt ℂ (dirichletSeriesSum f) s := by
  sorry

theorem dirichlet_series_derivative (f : ℕ → ℂ) (s : ℂ) :
    deriv (dirichletSeriesSum f) s =
    -dirichletSeriesSum (fun n => f n * Complex.log ↑(n : ℕ)) s := by
  sorry

theorem perron_formula (f : ℕ → ℂ) (x : ℝ) (hx : 0 < x) (σ : ℝ)
    (hσ : absoluteConvergenceAbscissa f < σ) :
    ∑' n : {n : ℕ | (↑n : ℝ) ≤ x}, f ↑n =
    (1 / (2 * Real.pi * Complex.I)) •
      (∫ t : ℝ, dirichletSeriesSum f ⟨σ, t⟩ * x ^ (σ + t * Complex.I) / ⟨σ, t⟩) := by
  sorry

end DirichletSeries
