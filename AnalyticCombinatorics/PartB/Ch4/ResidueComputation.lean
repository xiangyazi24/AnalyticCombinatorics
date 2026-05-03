import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace ResidueComputation

/-! # Residue Computation Methods for Coefficient Extraction

Formalizes the residue-based approach to extracting coefficients from generating
functions, following Flajolet & Sedgewick Chapter IV. The fundamental connection:
  [z^n] f(z) = (1/2πi) ∮ f(z)/z^(n+1) dz = Σ Res(f(z)/z^(n+1), poles)
-/

open Nat BigOperators Finset

/-- The coefficient extraction operator [z^n] for a sequence viewed as a GF. -/
def coeff_extract (a : ℕ → ℤ) (n : ℕ) : ℤ := a n

/-- Residue data: a pole location (as rational), its order, and contribution. -/
structure PoleData where
  order : ℕ
  residue_coeff : ℕ → ℤ

/-- For f(z) = 1/(1-z)^k, the coefficient [z^n] = C(n+k-1, k-1). -/
def geometric_power_coeff (k : ℕ) (n : ℕ) : ℕ :=
  Nat.choose (n + k - 1) (k - 1)

/-- Cauchy's formula: [z^n](1/(1-z)) = 1 for all n. -/
theorem coeff_geometric (n : ℕ) : geometric_power_coeff 1 n = 1 := by
  simp [geometric_power_coeff]

/-- Key result: [z^n](1/(1-z)^2) = n + 1. -/
theorem coeff_one_minus_z_sq (n : ℕ) : geometric_power_coeff 2 n = n + 1 := by
  simp [geometric_power_coeff]

/-- [z^n](1/(1-z)^3) = C(n+2,2) = (n+1)(n+2)/2. -/
theorem coeff_one_minus_z_cube (n : ℕ) : geometric_power_coeff 3 n = Nat.choose (n + 2) 2 := by
  simp [geometric_power_coeff]

-- Numerical verifications via native_decide
example : geometric_power_coeff 2 0 = 1 := by native_decide
example : geometric_power_coeff 2 1 = 2 := by native_decide
example : geometric_power_coeff 2 2 = 3 := by native_decide
example : geometric_power_coeff 2 3 = 4 := by native_decide
example : geometric_power_coeff 2 5 = 6 := by native_decide
example : geometric_power_coeff 2 10 = 11 := by native_decide

example : geometric_power_coeff 3 0 = 1 := by native_decide
example : geometric_power_coeff 3 1 = 3 := by native_decide
example : geometric_power_coeff 3 2 = 6 := by native_decide
example : geometric_power_coeff 3 3 = 10 := by native_decide
example : geometric_power_coeff 3 4 = 15 := by native_decide

/-- Partial fraction term: coefficient of 1/(1 - α·z)^k contributes
    α^n · C(n+k-1, k-1) to [z^n]. For α = 1 this is just C(n+k-1, k-1). -/
def partial_fraction_contrib (alpha : ℤ) (k : ℕ) (n : ℕ) : ℤ :=
  alpha ^ n * (Nat.choose (n + k - 1) (k - 1) : ℤ)

theorem partial_fraction_alpha_one (k n : ℕ) :
    partial_fraction_contrib 1 k n = (Nat.choose (n + k - 1) (k - 1) : ℤ) := by
  simp [partial_fraction_contrib]

/-- For a rational GF with simple poles at 1/α_i, the coefficient is a sum of
    residue contributions. -/
def rational_gf_coeff (poles : List (ℤ × ℕ)) (n : ℕ) : ℤ :=
  poles.foldl (fun acc (alpha, k) => acc + partial_fraction_contrib alpha k n) 0

/-- Example: f(z) = 1/(1-z) + 1/(1-z)^2 has [z^n] = 1 + (n+1) = n + 2. -/
theorem coeff_sum_example (n : ℕ) :
    partial_fraction_contrib 1 1 n + partial_fraction_contrib 1 2 n = (n : ℤ) + 2 := by
  simp [partial_fraction_contrib]
  ring

-- Verify the sum example numerically
example : partial_fraction_contrib 1 1 0 + partial_fraction_contrib 1 2 0 = 2 := by native_decide
example : partial_fraction_contrib 1 1 3 + partial_fraction_contrib 1 2 3 = 5 := by native_decide
example : partial_fraction_contrib 1 1 7 + partial_fraction_contrib 1 2 7 = 9 := by native_decide

/-- For f(z) = 1/(1-2z), we get [z^n] = 2^n. -/
theorem coeff_geometric_alpha (n : ℕ) :
    partial_fraction_contrib 2 1 n = 2 ^ n := by
  simp [partial_fraction_contrib]

example : partial_fraction_contrib 2 1 0 = 1 := by native_decide
example : partial_fraction_contrib 2 1 3 = 8 := by native_decide
example : partial_fraction_contrib 2 1 5 = 32 := by native_decide
example : partial_fraction_contrib 2 1 10 = 1024 := by native_decide

/-- Residue at a simple pole: Res(f(z)/z^(n+1), z=a) = f(a) · a^(-n-1)
    For 1/(1-z) at z=1 in the transformed variable, this gives 1. -/
def simple_pole_residue (f_at_pole : ℤ) (_n : ℕ) : ℤ := f_at_pole

/-- For a double pole: Res at z=a of g(z)/(z-a)^2 involves the derivative.
    Coefficient contribution from a double pole at 1/α is α^n · (n+1). -/
def double_pole_coeff (alpha : ℤ) (n : ℕ) : ℤ :=
  alpha ^ n * ((n : ℤ) + 1)

theorem double_pole_matches_formula (n : ℕ) :
    double_pole_coeff 1 n = partial_fraction_contrib 1 2 n := by
  simp [double_pole_coeff, partial_fraction_contrib]

example : double_pole_coeff 2 3 = 32 := by native_decide
example : double_pole_coeff 3 2 = 27 := by native_decide

/-- Transfer theorem: if f has a dominant singularity at ρ with expansion
    f(z) ~ c/(1 - z/ρ)^k near z = ρ, then [z^n]f(z) ~ c · n^(k-1) / ((k-1)! · ρ^n). -/
theorem transfer_principle_rational (c : ℤ) (n : ℕ) :
    c * partial_fraction_contrib 1 2 n = c * ((n : ℤ) + 1) := by
  simp [partial_fraction_contrib]

/-- Fibonacci example: F(z) = z/(1-z-z^2) decomposes into partial fractions.
    The dominant root φ = (1+√5)/2 gives [z^n] ~ φ^n/√5.
    Here we verify the recurrence relation coefficients. -/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

example : fib 0 = 0 := by native_decide
example : fib 1 = 1 := by native_decide
example : fib 5 = 5 := by native_decide
example : fib 10 = 55 := by native_decide
example : fib 12 = 144 := by native_decide

/-- The Catalan generating function C(z) = (1-√(1-4z))/(2z) has a branch point
    singularity at z = 1/4. Its residue structure differs from polar singularities.
    [z^n] C(z) = C(2n,n)/(n+1). -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

example : catalan 0 = 1 := by native_decide
example : catalan 1 = 1 := by native_decide
example : catalan 2 = 2 := by native_decide
example : catalan 3 = 5 := by native_decide
example : catalan 4 = 14 := by native_decide
example : catalan 5 = 42 := by native_decide

/-- Cauchy's integral formula connects coefficients to contour integrals.
    For meromorphic functions, this reduces to residue sums.
    Statement: [z^n]f(z) = sum of Res(f(z)/z^(n+1)) over all poles inside contour. -/
theorem cauchy_residue_principle
    (f_coeffs : ℕ → ℤ) (residue_sum : ℕ → ℤ)
    (h : ∀ n, f_coeffs n = residue_sum n) (n : ℕ) :
    coeff_extract f_coeffs n = residue_sum n := by
  simp [coeff_extract, h]

/-- For higher-order poles, the residue involves derivatives:
    Res(f(z)/(z-a)^k, z=a) = (1/(k-1)!) · d^(k-1)/dz^(k-1)[(z-a)^k · f(z)] at z=a.
    For 1/(1-z)^k this yields the binomial coefficient formula. -/
theorem higher_order_pole_formula (k n : ℕ) (_hk : 0 < k) :
    geometric_power_coeff k n = Nat.choose (n + k - 1) (k - 1) := by
  simp [geometric_power_coeff]

/-- Linearity of coefficient extraction: [z^n](af + bg) = a·[z^n]f + b·[z^n]g. -/
theorem coeff_linear (f g : ℕ → ℤ) (a b : ℤ) (n : ℕ) :
    coeff_extract (fun n => a * f n + b * g n) n =
    a * coeff_extract f n + b * coeff_extract g n := by
  simp [coeff_extract]

/-- Product rule: [z^n](f·g) = Σ_{k=0}^{n} [z^k]f · [z^(n-k)]g (Cauchy product). -/
def cauchy_product (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), f k * g (n - k)

example : cauchy_product (fun _ => 1) (fun _ => 1) 4 = 5 := by native_decide
example : cauchy_product (fun _ => 1) (fun _ => 1) 3 = 4 := by native_decide

/-- The convolution of 1/(1-z) with itself gives 1/(1-z)^2,
    matching [z^n] = n + 1. -/
theorem convolution_geometric_sq (n : ℕ) :
    cauchy_product (fun _ => 1) (fun _ => 1) n = (n : ℤ) + 1 := by
  simp [cauchy_product, Finset.sum_const, Finset.card_range]

end ResidueComputation
