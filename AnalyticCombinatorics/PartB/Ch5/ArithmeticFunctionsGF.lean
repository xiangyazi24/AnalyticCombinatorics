import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace ArithmeticFunctionsGF

/-!
# Arithmetic Functions and Dirichlet Convolution

Divisor power sums σ_k, von Mangoldt function Λ, Jordan's totient J_k,
Dirichlet inverse, and connections between multiplicative arithmetic functions
and their Dirichlet series / prime factorization generating functions.

Reference: Flajolet & Sedgewick, Analytic Combinatorics, Part B, Chapter 5.
-/

/-! ## Core Arithmetic Functions -/

def divisorsOf (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun d => d ≥ 1 ∧ n % d = 0

def mobius (n : ℕ) : Int :=
  if n = 0 then 0
  else if n = 1 then 1
  else if !((List.range (n - 1)).any fun i => n % ((i + 2) * (i + 2)) == 0)
    then (-1) ^ ((Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ n % p = 0).card
    else 0

def constOne : ℕ → Int := fun _ => 1
def identFun : ℕ → Int := fun n => ↑n
def kronecker : ℕ → Int := fun n => if n = 1 then 1 else 0

/-! ## 2: Dirichlet Convolution Algebra -/


def dirichletConv (f g : ℕ → Int) (n : ℕ) : Int :=
  (divisorsOf n).sum fun d => f d * g (n / d)

theorem dirichlet_conv_comm (f g : ℕ → Int) (n : ℕ) :
    dirichletConv f g n = dirichletConv g f n := by
  sorry

theorem dirichlet_conv_identity_left (f : ℕ → Int) (n : ℕ) (hn : n > 0) :
    dirichletConv kronecker f n = f n := by
  sorry

theorem dirichlet_conv_identity_right (f : ℕ → Int) (n : ℕ) (hn : n > 0) :
    dirichletConv f kronecker n = f n := by
  sorry

/-! ## 3: Dirichlet Inverse -/


def dirichletInverse (f : ℕ → Int) (n : ℕ) : Int :=
  if n = 0 then 0
  else if n = 1 then if f 1 = 1 ∨ f 1 = -1 then f 1 else 0
  else -((divisorsOf n).filter fun d => d ≥ 1 ∧ d < n).sum fun d =>
    f (n / d) * dirichletInverse f d
  termination_by n
  decreasing_by sorry

theorem dirichlet_inverse_spec (f : ℕ → Int) (hf : f 1 = 1) (n : ℕ) (hn : n > 0) :
    dirichletConv f (dirichletInverse f) n = kronecker n := by
  sorry

-- μ is the Dirichlet inverse of 1
example : dirichletConv mobius constOne 1 = kronecker 1 := by native_decide
example : dirichletConv mobius constOne 6 = kronecker 6 := by native_decide
example : dirichletConv mobius constOne 12 = kronecker 12 := by native_decide

/-! ## 4: Divisor Power Sums σ_k -/


def sigmak (k : ℕ) (n : ℕ) : ℕ :=
  (divisorsOf n).sum fun d => d ^ k

def numDivisors (n : ℕ) : ℕ := sigmak 0 n
def sumDivisors (n : ℕ) : ℕ := sigmak 1 n

example : numDivisors 12 = 6 := by native_decide
example : numDivisors 24 = 8 := by native_decide
example : sumDivisors 6 = 12 := by native_decide
example : sumDivisors 28 = 56 := by native_decide

def sigma2 (n : ℕ) : ℕ := sigmak 2 n
example : sigma2 6 = 50 := by native_decide

-- σ_k is multiplicative
theorem sigmak_multiplicative (k : ℕ) (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (hc : Nat.Coprime m n) :
    sigmak k (m * n) = sigmak k m * sigmak k n := by
  sorry

/-! ## 5: Jordan's Totient Function J_k -/


def jordanTotient (k : ℕ) (n : ℕ) : Int :=
  (divisorsOf n).sum fun d => mobius d * ↑((n / d) ^ k)

example : jordanTotient 1 1 = 1 := by native_decide
example : jordanTotient 1 6 = 2 := by native_decide
example : jordanTotient 1 12 = 4 := by native_decide

example : jordanTotient 2 1 = 1 := by native_decide
example : jordanTotient 2 6 = 24 := by native_decide
example : jordanTotient 2 12 = 96 := by native_decide

-- J_k * 1 = id^k  (Dirichlet convolution identity)
def jordanConvOne (k : ℕ) (n : ℕ) : Int :=
  (divisorsOf n).sum fun d => jordanTotient k d

example : jordanConvOne 1 6 = 6 := by native_decide
example : jordanConvOne 1 12 = 12 := by native_decide
example : jordanConvOne 2 6 = 36 := by native_decide
example : jordanConvOne 2 12 = 144 := by native_decide

theorem jordan_divisor_sum (k : ℕ) (n : ℕ) (hn : n > 0) :
    jordanConvOne k n = ↑(n ^ k) := by
  sorry

/-! ## 6: Von Mangoldt Function -/


def isPrimePower (n : ℕ) : Bool :=
  if n < 2 then false
  else
    let p := n.minFac
    Nat.Prime p ∧ n = p ^ (Nat.log p n)

example : isPrimePower 2 = true := by native_decide
example : isPrimePower 4 = true := by native_decide
example : isPrimePower 8 = true := by native_decide
example : isPrimePower 6 = false := by native_decide
example : isPrimePower 10 = false := by native_decide
example : isPrimePower 1 = false := by native_decide

theorem vonMangoldt_mobius_identity (n : ℕ) (hn : n > 0) :
    ∀ f : ℕ → ℝ, (∀ m, m > 0 → f m = Real.log m) →
    (divisorsOf n).sum (fun d => (mobius d : ℝ) * f (n / d)) =
    if isPrimePower n then f n.minFac * ↑(Nat.log n.minFac n) else 0 := by
  sorry

/-! ## 7: Dirichlet Series as GF for Arithmetic Functions -/


noncomputable def dirichletGF (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, f (n + 1) / (↑(n + 1 : ℕ) : ℂ) ^ s

theorem dirichletGF_product (f g : ℕ → ℂ) (s : ℂ) :
    dirichletGF f s * dirichletGF g s =
    dirichletGF (fun n => (Nat.divisors n).sum fun d => f d * g (n / d)) s := by
  sorry

theorem zeta_squared_is_divisor_count (s : ℂ) :
    dirichletGF (fun _ => (1 : ℂ)) s ^ 2 =
    dirichletGF (fun n => ↑(Nat.divisors n).card) s := by
  sorry

theorem inverse_zeta_is_mobius (s : ℂ) :
    dirichletGF (fun _ => (1 : ℂ)) s * dirichletGF (fun n => ↑(mobius n)) s =
    dirichletGF (fun n => ↑(kronecker n)) s := by
  sorry

/-! ## 8: Prime Factorization GFs and Euler Products -/


def IsMultiplicative (f : ℕ → Int) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, m > 0 → n > 0 → Nat.Coprime m n →
    f (m * n) = f m * f n

theorem mobius_multiplicative : IsMultiplicative mobius := by
  sorry

theorem euler_totient_multiplicative :
    IsMultiplicative (fun n => ↑(Nat.totient n)) := by
  sorry

theorem mult_determined_by_prime_powers (f g : ℕ → Int)
    (hf : IsMultiplicative f) (hg : IsMultiplicative g)
    (h : ∀ p : ℕ, Nat.Prime p → ∀ k : ℕ, k ≥ 1 → f (p ^ k) = g (p ^ k)) :
    ∀ n : ℕ, n ≥ 1 → f n = g n := by
  sorry

theorem dirichletConv_multiplicative (f g : ℕ → Int)
    (hf : IsMultiplicative f) (hg : IsMultiplicative g) :
    IsMultiplicative (dirichletConv f g) := by
  sorry

/-! ## 9: Arithmetic Identities via Convolution -/


example : dirichletConv identFun constOne 12 = ↑(sumDivisors 12) := by native_decide  -- σ = id * 1
example : dirichletConv constOne constOne 12 = ↑(numDivisors 12) := by native_decide  -- d = 1 * 1
example : dirichletConv mobius identFun 12 = ↑(Nat.totient 12) := by native_decide    -- φ = μ * id
example : dirichletConv mobius identFun 30 = ↑(Nat.totient 30) := by native_decide

/-! ## 10: Numerical Tables and Cross-Checks -/


def sigmaTable : Fin 12 → ℕ :=
  ![1, 3, 4, 7, 6, 12, 8, 15, 13, 18, 12, 28]

def numDivTable : Fin 12 → ℕ :=
  ![1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 6]

def totientTable : Fin 12 → ℕ :=
  ![1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4]

def mobiusTable : Fin 12 → Int :=
  ![1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0]

theorem sigma_table_correct :
    ∀ i : Fin 12, sigmaTable i = sumDivisors (i.val + 1) := by native_decide

theorem numDiv_table_correct :
    ∀ i : Fin 12, numDivTable i = numDivisors (i.val + 1) := by native_decide

theorem totient_table_correct :
    ∀ i : Fin 12, totientTable i = Nat.totient (i.val + 1) := by native_decide

theorem mobius_table_correct :
    ∀ i : Fin 12, mobiusTable i = mobius (i.val + 1) := by native_decide

theorem six_is_perfect : sumDivisors 6 = 2 * 6 := by native_decide
theorem twentyeight_is_perfect : sumDivisors 28 = 2 * 28 := by native_decide

theorem sigma_mult_check :
    sumDivisors (2 * 3) = sumDivisors 2 * sumDivisors 3 := by native_decide

end ArithmeticFunctionsGF
