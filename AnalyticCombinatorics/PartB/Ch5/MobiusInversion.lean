import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace MobiusInversion

/-! # Möbius Inversion on Posets and Generating Functions

Flajolet & Sedgewick, Chapter V: The Möbius function μ(n) on the
divisibility poset, Dirichlet convolution, and Euler's totient
via Möbius inversion. -/

-- ============================================================
-- Section 1: Möbius Function
-- ============================================================

def primeFactors (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ n % p = 0

def isSquareFreeB (n : ℕ) : Bool :=
  !((List.range (n - 1)).any fun i => n % ((i + 2) * (i + 2)) == 0)

def mobius (n : ℕ) : Int :=
  if n = 0 then 0
  else if n = 1 then 1
  else if isSquareFreeB n then (-1) ^ (primeFactors n).card
  else 0

-- ============================================================
-- Section 2: Verification of Key Values
-- ============================================================

example : mobius 1 = 1 := by native_decide
example : mobius 6 = 1 := by native_decide
example : mobius 30 = -1 := by native_decide
example : mobius 12 = 0 := by native_decide

example : mobius 2 = -1 := by native_decide
example : mobius 3 = -1 := by native_decide
example : mobius 5 = -1 := by native_decide
example : mobius 29 = -1 := by native_decide
example : mobius 4 = 0 := by native_decide
example : mobius 9 = 0 := by native_decide
example : mobius 10 = 1 := by native_decide
example : mobius 14 = 1 := by native_decide
example : mobius 15 = 1 := by native_decide

-- ============================================================
-- Section 3: Divisors
-- ============================================================

def divisorsOf (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun d => d ≥ 1 ∧ n % d = 0

def numDivisors (n : ℕ) : ℕ := (divisorsOf n).card
def sumDivisors (n : ℕ) : ℕ := (divisorsOf n).sum id

example : numDivisors 12 = 6 := by native_decide
example : numDivisors 30 = 8 := by native_decide
example : sumDivisors 6 = 12 := by native_decide
example : sumDivisors 12 = 28 := by native_decide

-- ============================================================
-- Section 4: Summatory Möbius — Σ_{d|n} μ(d) = [n = 1]
-- ============================================================

def mobiusSum (n : ℕ) : Int :=
  (divisorsOf n).sum fun d => mobius d

example : mobiusSum 1 = 1 := by native_decide
example : mobiusSum 2 = 0 := by native_decide
example : mobiusSum 6 = 0 := by native_decide
example : mobiusSum 12 = 0 := by native_decide
example : mobiusSum 30 = 0 := by native_decide

theorem mobiusSum_eq_kronecker (n : ℕ) (hn : n > 0) :
    mobiusSum n = if n = 1 then 1 else 0 := by
  sorry

-- ============================================================
-- Section 5: Euler's Totient
-- ============================================================

def eulerTotient (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun k => k ≥ 1 ∧ Nat.gcd k n = 1).card

example : eulerTotient 1 = 1 := by native_decide
example : eulerTotient 6 = 2 := by native_decide
example : eulerTotient 12 = 4 := by native_decide
example : eulerTotient 30 = 8 := by native_decide

def totientDivisorSum (n : ℕ) : ℕ :=
  (divisorsOf n).sum fun d => eulerTotient d

example : totientDivisorSum 1 = 1 := by native_decide
example : totientDivisorSum 6 = 6 := by native_decide
example : totientDivisorSum 12 = 12 := by native_decide
example : totientDivisorSum 30 = 30 := by native_decide

theorem gauss_totient_sum (n : ℕ) (hn : n > 0) :
    totientDivisorSum n = n := by
  sorry

-- ============================================================
-- Section 6: Totient via Möbius Inversion
-- ============================================================

/-! φ(n) = Σ_{d|n} μ(d)·(n/d) — Möbius inversion of Gauss's identity -/

def totientViaMobius (n : ℕ) : Int :=
  (divisorsOf n).sum fun d => mobius d * (↑(n / d))

example : totientViaMobius 1 = 1 := by native_decide
example : totientViaMobius 6 = 2 := by native_decide
example : totientViaMobius 12 = 4 := by native_decide
example : totientViaMobius 30 = 8 := by native_decide

example : totientViaMobius 1 = ↑(eulerTotient 1) := by native_decide
example : totientViaMobius 6 = ↑(eulerTotient 6) := by native_decide
example : totientViaMobius 12 = ↑(eulerTotient 12) := by native_decide
example : totientViaMobius 30 = ↑(eulerTotient 30) := by native_decide

-- ============================================================
-- Section 7: Dirichlet Convolution
-- ============================================================

/-! (f ⊛ g)(n) = Σ_{d|n} f(d)·g(n/d) — multiplication of Dirichlet series -/

def dirichletConv (f g : ℕ → Int) (n : ℕ) : Int :=
  (divisorsOf n).sum fun d => f d * g (n / d)

def constOne : ℕ → Int := fun _ => 1
def identFun : ℕ → Int := fun n => ↑n
def kronecker : ℕ → Int := fun n => if n = 1 then 1 else 0

-- μ ⊛ 1 = ε
example : dirichletConv mobius constOne 1 = kronecker 1 := by native_decide
example : dirichletConv mobius constOne 6 = kronecker 6 := by native_decide
example : dirichletConv mobius constOne 12 = kronecker 12 := by native_decide
example : dirichletConv mobius constOne 30 = kronecker 30 := by native_decide

-- μ ⊛ id = φ
example : dirichletConv mobius identFun 6 = ↑(eulerTotient 6) := by native_decide
example : dirichletConv mobius identFun 12 = ↑(eulerTotient 12) := by native_decide
example : dirichletConv mobius identFun 30 = ↑(eulerTotient 30) := by native_decide

theorem dirichlet_conv_assoc (f g h : ℕ → Int) (n : ℕ) (hn : n > 0) :
    dirichletConv (dirichletConv f g) h n =
    dirichletConv f (dirichletConv g h) n := by
  sorry

-- ============================================================
-- Section 8: Möbius Inversion Formula
-- ============================================================

theorem mobius_inversion
    (f g : ℕ → Int)
    (hg : ∀ n > 0, g n = (divisorsOf n).sum fun d => f d)
    (n : ℕ) (hn : n > 0) :
    f n = (divisorsOf n).sum fun d => mobius d * g (n / d) := by
  sorry

-- ============================================================
-- Section 9: Interval Möbius on Divisibility Poset
-- ============================================================

def intervalMobius (a b : ℕ) : Int :=
  if a = 0 ∨ b = 0 ∨ b % a ≠ 0 then 0
  else mobius (b / a)

example : intervalMobius 1 6 = mobius 6 := by native_decide
example : intervalMobius 2 6 = mobius 3 := by native_decide
example : intervalMobius 3 6 = mobius 2 := by native_decide
example : intervalMobius 6 6 = mobius 1 := by native_decide

def intervalMobiusSum (a b : ℕ) : Int :=
  ((divisorsOf b).filter fun d => d % a = 0).sum fun d => intervalMobius a d

example : intervalMobiusSum 1 1 = 1 := by native_decide
example : intervalMobiusSum 1 6 = 0 := by native_decide
example : intervalMobiusSum 2 12 = 0 := by native_decide
example : intervalMobiusSum 6 6 = 1 := by native_decide

-- ============================================================
-- Section 10: Mertens Function (Partial Sums of μ)
-- ============================================================

/-! M(N) = Σ_{n=1}^{N} μ(n). The DGF of μ is 1/ζ(s), connecting
    Möbius inversion to the GF identity G(s)=F(s)ζ(s) ⟺ F(s)=G(s)/ζ(s). -/

def mertensFun (N : ℕ) : Int :=
  (Finset.range N).sum fun n => mobius (n + 1)

example : mertensFun 1 = 1 := by native_decide
example : mertensFun 6 = -1 := by native_decide
example : mertensFun 10 = -1 := by native_decide

end MobiusInversion
