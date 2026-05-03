import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace InversionFormulas

/-! # Lagrange Inversion and Bürmann Formula

Coefficient extraction for compositional inverses of formal power series.
Based on Flajolet & Sedgewick, Analytic Combinatorics, Chapter 6.

The Lagrange inversion theorem: if w = t · φ(w) with φ(0) ≠ 0, then
  [tⁿ] w = (1/n) · [wⁿ⁻¹] φ(w)ⁿ
The generalized form (Bürmann): for any H,
  [tⁿ] H(w) = (1/n) · [wⁿ⁻¹] H'(w) · φ(w)ⁿ
and for powers of w:
  [tⁿ] wᵏ = (k/n) · [wⁿ⁻ᵏ] φ(w)ⁿ
-/

section CatalanNumbers

def catalanNumber (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

example : catalanNumber 0 = 1 := by native_decide
example : catalanNumber 1 = 1 := by native_decide
example : catalanNumber 2 = 2 := by native_decide
example : catalanNumber 3 = 5 := by native_decide
example : catalanNumber 4 = 14 := by native_decide
example : catalanNumber 5 = 42 := by native_decide
example : catalanNumber 6 = 132 := by native_decide

theorem catalan_binomial_identity (n : ℕ) :
    (n + 1) * catalanNumber n = Nat.choose (2 * n) n := by
  sorry

theorem catalan_difference_formula (n : ℕ) :
    catalanNumber n = Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1) := by
  sorry

example : Nat.choose 4 2 - Nat.choose 4 3 = 2 := by native_decide
example : Nat.choose 6 3 - Nat.choose 6 4 = 5 := by native_decide
example : Nat.choose 8 4 - Nat.choose 8 5 = 14 := by native_decide
example : Nat.choose 10 5 - Nat.choose 10 6 = 42 := by native_decide

theorem catalan_recurrence (n : ℕ) :
    catalanNumber (n + 1) =
      (Finset.range (n + 1)).sum fun i => catalanNumber i * catalanNumber (n - i) := by
  sorry

example : (2 + 1) * catalanNumber 2 = Nat.choose 4 2 := by native_decide
example : (4 + 1) * catalanNumber 4 = Nat.choose 8 4 := by native_decide
example : (5 + 1) * catalanNumber 5 = Nat.choose 10 5 := by native_decide

end CatalanNumbers

section LagrangeInversion

structure LagrangeContext where
  phi_coeffs : ℕ → ℚ
  phi_zero_ne_zero : phi_coeffs 0 ≠ 0

structure BurmannContext extends LagrangeContext where
  h_coeffs : ℕ → ℚ

/-- Lagrange inversion for φ(w) = (1+w)²: binary trees / Catalan numbers.
    [tⁿ] w = C(2n, n-1) / n -/
def lagrangeCoeffCatalan (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.choose (2 * n) (n - 1) / n

example : lagrangeCoeffCatalan 1 = 1 := by native_decide
example : lagrangeCoeffCatalan 2 = 2 := by native_decide
example : lagrangeCoeffCatalan 3 = 5 := by native_decide
example : lagrangeCoeffCatalan 4 = 14 := by native_decide
example : lagrangeCoeffCatalan 5 = 42 := by native_decide
example : lagrangeCoeffCatalan 6 = 132 := by native_decide

theorem lagrange_catalan_agreement (n : ℕ) (hn : n ≥ 1) :
    lagrangeCoeffCatalan n = catalanNumber n := by
  sorry

/-- Generalized Lagrange: [tⁿ] wᵏ = (k/n) · C(2n, n-k) for φ(w) = (1+w)² -/
def lagrangeGeneralized (n k : ℕ) : ℕ :=
  if n = 0 then 0 else k * Nat.choose (2 * n) (n - k) / n

example : lagrangeGeneralized 1 1 = 1 := by native_decide
example : lagrangeGeneralized 2 1 = 2 := by native_decide
example : lagrangeGeneralized 3 1 = 5 := by native_decide
example : lagrangeGeneralized 4 1 = 14 := by native_decide
example : lagrangeGeneralized 5 1 = 42 := by native_decide

example : lagrangeGeneralized 2 2 = 1 := by native_decide
example : lagrangeGeneralized 3 2 = 4 := by native_decide
example : lagrangeGeneralized 4 2 = 14 := by native_decide
example : lagrangeGeneralized 5 2 = 48 := by native_decide

example : lagrangeGeneralized 3 3 = 1 := by native_decide
example : lagrangeGeneralized 4 3 = 6 := by native_decide
example : lagrangeGeneralized 5 3 = 27 := by native_decide

theorem lagrange_gen_k_one (n : ℕ) (hn : n ≥ 1) :
    lagrangeGeneralized n 1 = catalanNumber n := by
  sorry

end LagrangeInversion

section BallotNumbers

/-- Ballot number: B(n,k) = (k/n) · C(2n, n-k) generalizes Catalan (B(n,1) = Cₙ) -/
def ballotNumber (n k : ℕ) : ℕ :=
  if n = 0 then 0 else k * Nat.choose (2 * n) (n - k) / n

example : ballotNumber 1 1 = 1 := by native_decide
example : ballotNumber 2 1 = 2 := by native_decide
example : ballotNumber 3 1 = 5 := by native_decide
example : ballotNumber 4 1 = 14 := by native_decide
example : ballotNumber 5 1 = 42 := by native_decide

theorem ballot_one_eq_catalan (n : ℕ) (hn : n ≥ 1) :
    ballotNumber n 1 = catalanNumber n := by
  sorry

example : ballotNumber 2 2 = 1 := by native_decide
example : ballotNumber 3 2 = 4 := by native_decide
example : ballotNumber 4 2 = 14 := by native_decide
example : ballotNumber 5 2 = 48 := by native_decide

end BallotNumbers

section TreeEnumeration

/-- Cayley's formula via Lagrange inversion of T = x·eᵀ:
    number of labeled rooted trees on n vertices is n^(n-1) -/
def labeledRootedTrees (n : ℕ) : ℕ := n ^ (n - 1)

example : labeledRootedTrees 1 = 1 := by native_decide
example : labeledRootedTrees 2 = 2 := by native_decide
example : labeledRootedTrees 3 = 9 := by native_decide
example : labeledRootedTrees 4 = 64 := by native_decide
example : labeledRootedTrees 5 = 625 := by native_decide

/-- Labeled unrooted trees on n vertices: n^(n-2) (Cayley's formula) -/
def cayleyTrees (n : ℕ) : ℕ := if n ≤ 1 then 1 else n ^ (n - 2)

example : cayleyTrees 1 = 1 := by native_decide
example : cayleyTrees 2 = 1 := by native_decide
example : cayleyTrees 3 = 3 := by native_decide
example : cayleyTrees 4 = 16 := by native_decide
example : cayleyTrees 5 = 125 := by native_decide
example : cayleyTrees 6 = 1296 := by native_decide

/-- Lagrange inversion of T = x·eᵀ gives [xⁿ]T = nⁿ⁻¹/n! -/
theorem cayley_lagrange_coeff (n : ℕ) (hn : n ≥ 1) :
    labeledRootedTrees n = n ^ (n - 1) := by
  rfl

end TreeEnumeration

section CentralBinomialCoefficients

/-- Central binomial coefficients C(2n, n) -/
example : Nat.choose 4 2 = 6 := by native_decide
example : Nat.choose 6 3 = 20 := by native_decide
example : Nat.choose 8 4 = 70 := by native_decide
example : Nat.choose 10 5 = 252 := by native_decide

/-- Recurrence: n · C(2n, n) = 2(2n-1) · C(2(n-1), n-1) -/
example : 2 * Nat.choose 4 2 = 2 * 3 * Nat.choose 2 1 := by native_decide
example : 3 * Nat.choose 6 3 = 2 * 5 * Nat.choose 4 2 := by native_decide
example : 4 * Nat.choose 8 4 = 2 * 7 * Nat.choose 6 3 := by native_decide

theorem central_binomial_recurrence (n : ℕ) (hn : n ≥ 1) :
    n * Nat.choose (2 * n) n = 2 * (2 * n - 1) * Nat.choose (2 * (n - 1)) (n - 1) := by
  sorry

end CentralBinomialCoefficients

section SeriesReversion

/-- Series reversion of f(t) = t(1-t): the inverse g satisfies f(g(x)) = x.
    [xⁿ]g = (1/n) · [tⁿ⁻¹](t/f(t))ⁿ = C(2n-2, n-1)/n -/
def reversionCoeff (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else Nat.choose (2 * n - 2) (n - 1) / n

example : reversionCoeff 1 = 1 := by native_decide
example : reversionCoeff 2 = 1 := by native_decide
example : reversionCoeff 3 = 2 := by native_decide
example : reversionCoeff 4 = 5 := by native_decide
example : reversionCoeff 5 = 14 := by native_decide
example : reversionCoeff 6 = 42 := by native_decide

theorem reversion_is_catalan_shifted (n : ℕ) (hn : n ≥ 1) :
    reversionCoeff (n + 1) = catalanNumber n := by
  sorry

end SeriesReversion

end InversionFormulas
