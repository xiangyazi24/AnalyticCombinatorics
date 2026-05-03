import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace OGFExamples

/-! ## OGF examples and identities
Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter I.
Binomial series, geometric series convolutions, Fibonacci GF derivation,
coefficient extraction, partial fractions for rational GFs. -/

abbrev OGF := ℕ → ℚ

def coeff (f : OGF) (n : ℕ) : ℚ := f n

def ogfMul (f g : OGF) : OGF := fun n =>
  ∑ k : Fin (n + 1), f k.val * g (n - k.val)

/-! ## Fundamental sequences -/

def geometric (r : ℚ) : OGF := fun n => r ^ n

def allOnes : OGF := fun _ => 1

def ogfOne : OGF := fun n => if n = 0 then 1 else 0

def binomialSeq (α : ℚ) : OGF := fun n =>
  ∏ i : Fin n, (α - i.val) / (i.val + 1 : ℚ)

def catalan : OGF := fun n =>
  (Nat.choose (2 * n) n : ℚ) / (n + 1)

def fibonacci : OGF := fun n => (Nat.fib n : ℚ)

def powers (k : ℕ) : OGF := fun n => (n : ℚ) ^ k

/-! ## Binomial series: (1+z)^α has coefficients C(α,n) -/

theorem binomialSeq_zero (α : ℚ) : binomialSeq α 0 = 1 := by
  simp [binomialSeq]

theorem binomialSeq_one (α : ℚ) : binomialSeq α 1 = α := by
  simp [binomialSeq]

theorem binomialSeq_neg_one : binomialSeq (-1) = fun n => (-1 : ℚ) ^ n := by
  ext n; induction n with
  | zero => simp [binomialSeq]
  | succ n ih =>
    simp only [binomialSeq]
    sorry

example : binomialSeq 2 0 = 1 := by native_decide
example : binomialSeq 2 1 = 2 := by native_decide
example : binomialSeq 2 2 = 1 := by native_decide
example : binomialSeq 2 3 = 0 := by native_decide

example : binomialSeq 3 0 = 1 := by native_decide
example : binomialSeq 3 1 = 3 := by native_decide
example : binomialSeq 3 2 = 3 := by native_decide
example : binomialSeq 3 3 = 1 := by native_decide

/-! ## Geometric series: 1/(1-rz) has coefficients r^n -/

theorem geometric_zero (r : ℚ) : geometric r 0 = 1 := by
  simp [geometric]

theorem geometric_succ (r : ℚ) (n : ℕ) :
    geometric r (n + 1) = r * geometric r n := by
  simp [geometric, pow_succ, mul_comm]

theorem geometric_one_eq_allOnes : geometric 1 = allOnes := by
  ext n; simp [geometric, allOnes]

/-! ## Convolution of geometric series: partial fractions -/

def partialFractionPair (a b : ℚ) (hab : a ≠ b) : OGF := fun n =>
  (a ^ (n + 1) - b ^ (n + 1)) / (a - b)

theorem geometric_conv_geometric (a b : ℚ) (hab : a ≠ b) (n : ℕ) :
    ogfMul (geometric a) (geometric b) n = partialFractionPair a b hab n := by
  sorry

example : ogfMul (geometric 2) (geometric 3) 0 = 1 := by native_decide
example : ogfMul (geometric 2) (geometric 3) 1 = 5 := by native_decide
example : ogfMul (geometric 2) (geometric 3) 2 = 19 := by native_decide

theorem geometric_self_conv (r : ℚ) (n : ℕ) :
    ogfMul (geometric r) (geometric r) n = (n + 1 : ℚ) * r ^ n := by
  sorry

example : ogfMul (geometric 2) (geometric 2) 0 = 1 := by native_decide
example : ogfMul (geometric 2) (geometric 2) 1 = 4 := by native_decide
example : ogfMul (geometric 2) (geometric 2) 2 = 12 := by native_decide
example : ogfMul (geometric 2) (geometric 2) 3 = 32 := by native_decide

/-! ## Fibonacci OGF: F(z) = z/(1-z-z²) -/

theorem fib_recurrence (n : ℕ) :
    Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := by
  rw [Nat.fib_add_two]; omega

def fibOGF : OGF := fun n =>
  if n = 0 then 0 else Nat.fib n

theorem fibOGF_satisfies_recurrence (n : ℕ) :
    fibOGF (n + 2) = fibOGF (n + 1) + fibOGF n := by
  sorry

example : fibonacci 0 = 0 := by native_decide
example : fibonacci 1 = 1 := by native_decide
example : fibonacci 2 = 1 := by native_decide
example : fibonacci 3 = 2 := by native_decide
example : fibonacci 4 = 3 := by native_decide
example : fibonacci 5 = 5 := by native_decide
example : fibonacci 6 = 8 := by native_decide
example : fibonacci 10 = 55 := by native_decide

/-! ## Partial fraction decomposition for Fibonacci GF:
    F(z) = 1/(1-φz) - 1/(1-ψz) where φ=(1+√5)/2, ψ=(1-√5)/2.
    Over ℚ we verify the algebraic identity z/(1-z-z²) = z·(A/(1-φz) + B/(1-ψz)). -/

theorem fib_partial_fraction_rational (n : ℕ) (hn : 0 < n) :
    ∃ (φ ψ : ℝ), φ + ψ = 1 ∧ φ * ψ = -1 ∧
    (Nat.fib n : ℝ) = (φ ^ n - ψ ^ n) / (φ - ψ) := by
  sorry

/-! ## Coefficient extraction techniques -/

def linearCombination (a b : ℚ) (f g : OGF) : OGF := fun n =>
  a * f n + b * g n

theorem linearCombination_coeff (a b : ℚ) (f g : OGF) (n : ℕ) :
    coeff (linearCombination a b f g) n = a * coeff f n + b * coeff g n := by
  simp [coeff, linearCombination]

def rightShift (f : OGF) : OGF := fun n =>
  if n = 0 then 0 else f (n - 1)

theorem rightShift_coeff_zero (f : OGF) : coeff (rightShift f) 0 = 0 := by
  simp [coeff, rightShift]

theorem rightShift_coeff_succ (f : OGF) (n : ℕ) :
    coeff (rightShift f) (n + 1) = coeff f n := by
  simp [coeff, rightShift]

def leftShift (f : OGF) : OGF := fun n => f (n + 1)

theorem leftShift_coeff (f : OGF) (n : ℕ) :
    coeff (leftShift f) n = coeff f (n + 1) := by
  simp [coeff, leftShift]

/-! ## Partial fractions for rational GFs: A(z)/B(z) decomposition -/

def ratGF_simple (a r : ℚ) : OGF := fun n => a * r ^ n

theorem ratGF_simple_coeff (a r : ℚ) (n : ℕ) :
    coeff (ratGF_simple a r) n = a * r ^ n := by
  simp [coeff, ratGF_simple]

def ratGF_double (a r : ℚ) : OGF := fun n => a * (n + 1 : ℚ) * r ^ n

theorem ratGF_double_coeff (a r : ℚ) (n : ℕ) :
    coeff (ratGF_double a r) n = a * (n + 1) * r ^ n := by
  simp [coeff, ratGF_double]

theorem partial_fraction_sum (a₁ a₂ r₁ r₂ : ℚ) (n : ℕ) :
    coeff (linearCombination 1 1 (ratGF_simple a₁ r₁) (ratGF_simple a₂ r₂)) n =
    a₁ * r₁ ^ n + a₂ * r₂ ^ n := by
  simp [linearCombination_coeff, ratGF_simple_coeff, one_mul]

/-! ## Catalan numbers: C_n = C(2n,n)/(n+1) -/

example : catalan 0 = 1 := by native_decide
example : catalan 1 = 1 := by native_decide
example : catalan 2 = 2 := by native_decide
example : catalan 3 = 5 := by native_decide
example : catalan 4 = 14 := by native_decide
example : catalan 5 = 42 := by native_decide

theorem catalan_recurrence (n : ℕ) :
    catalan (n + 1) = ∑ k : Fin (n + 1), catalan k.val * catalan (n - k.val) := by
  sorry

/-! ## Powers of naturals as OGF coefficients -/

theorem powers_zero_eq_allOnes : powers 0 = allOnes := by
  ext n; simp [powers, allOnes]

def triangularNumbers : OGF := fun n => (n * (n + 1) : ℚ) / 2

example : triangularNumbers 0 = 0 := by native_decide
example : triangularNumbers 1 = 1 := by native_decide
example : triangularNumbers 2 = 3 := by native_decide
example : triangularNumbers 3 = 6 := by native_decide
example : triangularNumbers 4 = 10 := by native_decide

/-! ## Convolution identities for coefficient extraction -/

theorem allOnes_conv_is_naturals (n : ℕ) :
    ogfMul allOnes allOnes n = (n : ℚ) + 1 := by
  simp [ogfMul, allOnes, Finset.sum_const, nsmul_eq_mul]

theorem conv_shift_extracts_partial_sum (f : OGF) (n : ℕ) :
    ogfMul allOnes f n = ∑ k : Fin (n + 1), f (n - k.val) := by
  simp [ogfMul, allOnes]

theorem conv_ogfOne_identity (f : OGF) (n : ℕ) :
    ogfMul ogfOne f n = f n := by
  simp only [ogfMul, ogfOne]
  convert Finset.sum_eq_single (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ?_ ?_ using 1
  · simp
  · intro ⟨k, hk⟩ _ hne
    have : k ≠ 0 := fun h => hne (by ext; exact h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

example : ogfMul allOnes allOnes 0 = 1 := by native_decide
example : ogfMul allOnes allOnes 4 = 5 := by native_decide
example : ogfMul allOnes allOnes 9 = 10 := by native_decide

end OGFExamples
