import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace HadamardProduct

/-!
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Hadamard Product and Diagonal Extraction

  The Hadamard product F ⊙ G of two GFs F(x) = Σ fₙ xⁿ, G(x) = Σ gₙ xⁿ
  is (F ⊙ G)(x) = Σ fₙ gₙ xⁿ (coefficient-wise multiplication).

  Given a bivariate GF F(x,y) = Σ a_{m,n} x^m y^n, the diagonal is
  Δ F(x) = Σ a_{n,n} x^n.  Key identity: Δ(f(x)·g(y)) = f ⊙ g.

  Reference: Flajolet & Sedgewick, Chapter VI, §VI.12.
-/

/-! ## 1. Hadamard product definition and coefficient sequences -/

def hadamardProd (f g : ℕ → ℚ) : ℕ → ℚ := fun n => f n * g n

def constSeq : ℕ → ℚ := fun _ => 1
def linearSeq : ℕ → ℚ := fun n => (n : ℚ) + 1
def geomSeq (r : ℚ) : ℕ → ℚ := fun n => r ^ n

-- Hadamard(1/(1-z), 1/(1-z)) = 1/(1-z): all coefficients are 1
example : hadamardProd constSeq constSeq 0 = 1 := by native_decide
example : hadamardProd constSeq constSeq 1 = 1 := by native_decide
example : hadamardProd constSeq constSeq 5 = 1 := by native_decide
example : hadamardProd constSeq constSeq 10 = 1 := by native_decide
example : hadamardProd constSeq constSeq 20 = 1 := by native_decide

-- Hadamard(1/(1-z), 1/(1-z)²) = 1/(1-z)²: coefficients n+1
example : hadamardProd constSeq linearSeq 0 = 1 := by native_decide
example : hadamardProd constSeq linearSeq 1 = 2 := by native_decide
example : hadamardProd constSeq linearSeq 4 = 5 := by native_decide
example : hadamardProd constSeq linearSeq 9 = 10 := by native_decide

-- Hadamard(1/(1-z)², 1/(1-z)²): coefficients (n+1)²
example : hadamardProd linearSeq linearSeq 0 = 1 := by native_decide
example : hadamardProd linearSeq linearSeq 1 = 4 := by native_decide
example : hadamardProd linearSeq linearSeq 2 = 9 := by native_decide
example : hadamardProd linearSeq linearSeq 3 = 16 := by native_decide
example : hadamardProd linearSeq linearSeq 4 = 25 := by native_decide

/-! ## 2. Algebraic properties -/

theorem hadamard_comm (f g : ℕ → ℚ) (n : ℕ) :
    hadamardProd f g n = hadamardProd g f n := by
  simp [hadamardProd, mul_comm]

theorem hadamard_assoc (f g h : ℕ → ℚ) (n : ℕ) :
    hadamardProd (hadamardProd f g) h n = hadamardProd f (hadamardProd g h) n := by
  simp [hadamardProd, mul_assoc]

theorem hadamard_identity (f : ℕ → ℚ) (n : ℕ) :
    hadamardProd constSeq f n = f n := by
  simp [hadamardProd, constSeq, one_mul]

theorem hadamard_zero (f : ℕ → ℚ) (n : ℕ) :
    hadamardProd (fun _ => 0) f n = 0 := by
  simp [hadamardProd]

theorem hadamard_add (f g h : ℕ → ℚ) (n : ℕ) :
    hadamardProd f (fun k => g k + h k) n = hadamardProd f g n + hadamardProd f h n := by
  simp [hadamardProd, mul_add]

/-! ## 3. Geometric Hadamard products: 1/(1-ax) ⊙ 1/(1-bx) = 1/(1-abx) -/

example : hadamardProd (geomSeq 2) (geomSeq 3) 0 = (geomSeq 6) 0 := by native_decide
example : hadamardProd (geomSeq 2) (geomSeq 3) 1 = (geomSeq 6) 1 := by native_decide
example : hadamardProd (geomSeq 2) (geomSeq 3) 2 = (geomSeq 6) 2 := by native_decide
example : hadamardProd (geomSeq 2) (geomSeq 3) 3 = (geomSeq 6) 3 := by native_decide
example : hadamardProd (geomSeq 2) (geomSeq 3) 4 = (geomSeq 6) 4 := by native_decide

theorem hadamard_geom (a b : ℚ) (n : ℕ) :
    hadamardProd (geomSeq a) (geomSeq b) n = geomSeq (a * b) n := by
  simp [hadamardProd, geomSeq, mul_pow]

/-! ## 4. Partial Hadamard sums -/

def hadamardPartialSum (f g : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1), hadamardProd f g k

example : hadamardPartialSum constSeq constSeq 0 = 1 := by native_decide
example : hadamardPartialSum constSeq constSeq 4 = 5 := by native_decide
example : hadamardPartialSum constSeq constSeq 9 = 10 := by native_decide

-- Σ_{k=0}^N (k+1) = (N+1)(N+2)/2
example : hadamardPartialSum constSeq linearSeq 0 = 1 := by native_decide
example : hadamardPartialSum constSeq linearSeq 3 = 10 := by native_decide
example : hadamardPartialSum constSeq linearSeq 5 = 21 := by native_decide

-- Σ_{k=0}^N (k+1)² = (N+1)(N+2)(2N+3)/6
example : hadamardPartialSum linearSeq linearSeq 0 = 1 := by native_decide
example : hadamardPartialSum linearSeq linearSeq 1 = 5 := by native_decide
example : hadamardPartialSum linearSeq linearSeq 2 = 14 := by native_decide
example : hadamardPartialSum linearSeq linearSeq 3 = 30 := by native_decide

/-! ## 5. Bivariate coefficients and diagonal extraction -/

def diagonalCoeff (a : ℕ → ℕ → ℚ) : ℕ → ℚ := fun n => a n n

-- 1/((1-x)(1-y)): a_{m,n} = 1 for all m,n
def constBivar : ℕ → ℕ → ℚ := fun _ _ => 1

-- Diagonal of 1/((1-x)(1-y)) = 1/(1-x)
example : diagonalCoeff constBivar 0 = 1 := by native_decide
example : diagonalCoeff constBivar 1 = 1 := by native_decide
example : diagonalCoeff constBivar 5 = 1 := by native_decide
example : diagonalCoeff constBivar 10 = 1 := by native_decide

-- 1/(1-x-y): a_{m,n} = C(m+n, m)
def binomBivar : ℕ → ℕ → ℚ := fun m n => (Nat.choose (m + n) m : ℚ)

example : binomBivar 0 0 = 1 := by native_decide
example : binomBivar 1 1 = 2 := by native_decide
example : binomBivar 2 1 = 3 := by native_decide
example : binomBivar 2 2 = 6 := by native_decide

-- Diagonal of 1/(1-x-y) has coefficients C(2n, n) (central binomial)
example : diagonalCoeff binomBivar 0 = 1 := by native_decide
example : diagonalCoeff binomBivar 1 = 2 := by native_decide
example : diagonalCoeff binomBivar 2 = 6 := by native_decide
example : diagonalCoeff binomBivar 3 = 20 := by native_decide
example : diagonalCoeff binomBivar 4 = 70 := by native_decide
example : diagonalCoeff binomBivar 5 = 252 := by native_decide

-- 1/(1-xy): a_{m,n} = δ_{m,n}
def diagOnlyBivar : ℕ → ℕ → ℚ := fun m n => if m = n then 1 else 0

example : diagonalCoeff diagOnlyBivar 0 = 1 := by native_decide
example : diagonalCoeff diagOnlyBivar 1 = 1 := by native_decide
example : diagonalCoeff diagOnlyBivar 5 = 1 := by native_decide
example : diagOnlyBivar 0 1 = 0 := by native_decide
example : diagOnlyBivar 2 3 = 0 := by native_decide

/-! ## 6. The diagonal-Hadamard connection: Δ(f(x)·g(y)) = f ⊙ g -/

def productBivar (f g : ℕ → ℚ) : ℕ → ℕ → ℚ := fun m n => f m * g n

theorem diagonal_of_product_eq_hadamard (f g : ℕ → ℚ) (n : ℕ) :
    diagonalCoeff (productBivar f g) n = hadamardProd f g n := by
  simp [diagonalCoeff, productBivar, hadamardProd]

example : diagonalCoeff (productBivar constSeq linearSeq) 3 =
    hadamardProd constSeq linearSeq 3 := by native_decide
example : diagonalCoeff (productBivar linearSeq linearSeq) 4 =
    hadamardProd linearSeq linearSeq 4 := by native_decide

/-! ## 7. Growth rate of diagonal coefficients -/

def centralBinomRatio (n : ℕ) : ℚ :=
  (Nat.choose (2 * (n + 1)) (n + 1) : ℚ) / (Nat.choose (2 * n) n : ℚ)

-- C(2(n+1), n+1) / C(2n, n) → 4 as n → ∞
example : centralBinomRatio 0 = 2 := by native_decide
example : centralBinomRatio 1 = 3 := by native_decide
example : centralBinomRatio 2 = 10 / 3 := by native_decide
example : centralBinomRatio 3 = 7 / 2 := by native_decide
example : centralBinomRatio 4 = 18 / 5 := by native_decide
example : centralBinomRatio 5 = 11 / 3 := by native_decide

def diagonalPartialSum (a : ℕ → ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1), diagonalCoeff a k

-- Cumulative sums of central binomial coefficients
example : diagonalPartialSum binomBivar 0 = 1 := by native_decide
example : diagonalPartialSum binomBivar 1 = 3 := by native_decide
example : diagonalPartialSum binomBivar 2 = 9 := by native_decide
example : diagonalPartialSum binomBivar 3 = 29 := by native_decide
example : diagonalPartialSum binomBivar 4 = 99 := by native_decide

/-! ## 8. Closure: Hadamard product of rational GFs is rational -/

theorem hadamard_rational_closure
    (f g : ℕ → ℚ)
    (hf : ∃ (d : ℕ) (c : Fin d → ℚ), ∀ n, f (n + d) = ∑ i : Fin d, c i * f (n + i))
    (hg : ∃ (d : ℕ) (c : Fin d → ℚ), ∀ n, g (n + d) = ∑ i : Fin d, c i * g (n + i)) :
    ∃ (d : ℕ) (c : Fin d → ℚ), ∀ n, hadamardProd f g (n + d) =
      ∑ i : Fin d, c i * hadamardProd f g (n + i) := by
  sorry

end HadamardProduct
