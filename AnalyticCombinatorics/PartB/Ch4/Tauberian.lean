import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace Tauberian

/-!
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Tauberian Theorems

  Numerical verifications and framework for:
  • Hardy-Littlewood Tauberian theorem (Abel means, one-sided conditions)
  • Abel summation by parts (the fundamental lemma)
  • Abelian-Tauberian coefficient asymptotics from singularity behavior
  • Karamata's regular variation framework
  • Monotone density theorem
-/

/-! ## 1. Abel means and the Hardy-Littlewood framework

  Hardy-Littlewood (1914): If aₙ ≥ 0 and f(x) = Σ aₙ xⁿ satisfies
  (1 − x) f(x) → s as x → 1⁻, then (1/(n+1)) Σ_{k=0}^n aₖ → s. -/

def abelPartialSum (a : ℕ → ℚ) (r : ℚ) (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1), a k * r ^ k

def abelMean (a : ℕ → ℚ) (r : ℚ) (N : ℕ) : ℚ :=
  (1 - r) * abelPartialSum a r N

def constSeq : ℕ → ℚ := fun _ => 1

-- For constant sequence: (1−r) Σ rᵏ = 1 − r^{N+1}
example : abelMean constSeq (1/2) 0  = 1 - (1/2) ^ 1  := by native_decide
example : abelMean constSeq (1/2) 5  = 1 - (1/2) ^ 6  := by native_decide
example : abelMean constSeq (1/2) 10 = 1 - (1/2) ^ 11 := by native_decide
example : abelMean constSeq (1/2) 19 = 1 - (1/2) ^ 20 := by native_decide
example : abelMean constSeq (3/4) 7  = 1 - (3/4) ^ 8  := by native_decide

/-! ## 2. Tauberian conditions and partial sums -/

def isNonnegUpTo (a : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun k => decide (0 ≤ a k)

def harmonicTerms (n : ℕ) : ℚ := 1 / ((n + 1 : ℕ) : ℚ)
example : isNonnegUpTo constSeq 50 = true := by native_decide
example : isNonnegUpTo harmonicTerms 50 = true := by native_decide

def partialSum (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), a k

example : partialSum harmonicTerms 0 = 1        := by native_decide
example : partialSum harmonicTerms 1 = 3 / 2    := by native_decide
example : partialSum harmonicTerms 2 = 11 / 6   := by native_decide
example : partialSum harmonicTerms 3 = 25 / 12  := by native_decide
example : partialSum harmonicTerms 5 = 49 / 20  := by native_decide

/-! ## 3. Abel summation by parts

  Σ_{k=0}^n aₖ bₖ = Sₙ bₙ − Σ_{k=0}^{n−1} Sₖ (bₖ₊₁ − bₖ)
  where Sₖ = Σ_{j=0}^k aⱼ. -/

def abelSumLHS (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), a k * b k

def abelSumRHS (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  partialSum a n * b n -
  ∑ k ∈ Finset.range n, partialSum a k * (b (k + 1) - b k)

def linearSeq (n : ℕ) : ℚ := ((n + 1 : ℕ) : ℚ)
def invLinearSeq (n : ℕ) : ℚ := 1 / ((n + 1 : ℕ) : ℚ)

-- aₖ = 1, bₖ = k + 1
example : abelSumLHS constSeq linearSeq 0 =
    abelSumRHS constSeq linearSeq 0 := by native_decide
example : abelSumLHS constSeq linearSeq 5 =
    abelSumRHS constSeq linearSeq 5 := by native_decide
example : abelSumLHS constSeq linearSeq 9 =
    abelSumRHS constSeq linearSeq 9 := by native_decide

-- aₖ = k + 1, bₖ = 1/(k + 1): both sides equal n + 1
example : abelSumLHS linearSeq invLinearSeq 0 =
    abelSumRHS linearSeq invLinearSeq 0 := by native_decide
example : abelSumLHS linearSeq invLinearSeq 9 =
    abelSumRHS linearSeq invLinearSeq 9 := by native_decide
example : abelSumLHS linearSeq invLinearSeq 9 = 10 := by
  native_decide

/-! ## 4. Abelian-Tauberian coefficient asymptotics

  [z^n](1−z)^{−α} = C(n+α−1, α−1) ~ n^{α−1}/Γ(α).
  Consecutive ratio [z^{n+1}]/[z^n] = (n+α)/(n+1) → 1. -/

structure AbelianTauberianPair where
  singularityExponent : ℚ
  coeffGrowthExponent : ℚ
  gammaFactor : ℚ
deriving DecidableEq

def mkATPair (alpha : ℕ) : AbelianTauberianPair :=
  { singularityExponent := (alpha : ℚ)
  , coeffGrowthExponent := (alpha : ℚ) - 1
  , gammaFactor := (Nat.factorial (alpha - 1) : ℚ) }

example : (mkATPair 1).coeffGrowthExponent = 0 := by native_decide
example : (mkATPair 2).coeffGrowthExponent = 1 := by native_decide
example : (mkATPair 3).coeffGrowthExponent = 2 := by native_decide
example : (mkATPair 1).gammaFactor = 1 := by native_decide
example : (mkATPair 3).gammaFactor = 2 := by native_decide
example : (mkATPair 4).gammaFactor = 6 := by native_decide
def singularityCoeff (alpha n : ℕ) : ℚ :=
  (Nat.choose (n + alpha - 1) (alpha - 1) : ℚ)

example : ∀ n : Fin 10,
    singularityCoeff 1 n.val = 1 := by native_decide
example : ∀ n : Fin 10,
    singularityCoeff 2 n.val = (n.val + 1 : ℚ) := by native_decide
example : ∀ n : Fin 10,
    singularityCoeff 3 n.val =
      ((n.val + 1) * (n.val + 2) : ℚ) / 2 := by native_decide
def coeffRatio (alpha n : ℕ) : ℚ :=
  if singularityCoeff alpha n = 0 then 0
  else singularityCoeff alpha (n + 1) / singularityCoeff alpha n

example : ∀ n : Fin 10,
    coeffRatio 2 n.val =
      ((n.val + 2 : ℕ) : ℚ) / ((n.val + 1 : ℕ) : ℚ) := by
  native_decide
example : ∀ n : Fin 10,
    coeffRatio 3 n.val =
      ((n.val + 3 : ℕ) : ℚ) / ((n.val + 1 : ℕ) : ℚ) := by
  native_decide

example : coeffRatio 2 99 = 101 / 100 := by native_decide
example : coeffRatio 3 99 = 102 / 100 := by native_decide
/-! ## 5. Fibonacci growth ratios (algebraic singularity)

  z/(1−z−z²) has singularity at ρ = (√5−1)/2.
  Ratio F_{n+1}/F_n → φ ≈ 1.618. -/

def fibRatio (n : ℕ) : ℚ :=
  if Nat.fib n = 0 then 0
  else (Nat.fib (n + 1) : ℚ) / (Nat.fib n : ℚ)

example : fibRatio 3  = 3 / 2   := by native_decide
example : fibRatio 5  = 8 / 5   := by native_decide
example : fibRatio 7  = 21 / 13 := by native_decide
example : fibRatio 9  = 55 / 34 := by native_decide
example : fibRatio 10 = 89 / 55 := by native_decide

-- All ratios from index 3 onward bracket φ in [3/2, 5/3]
example : ∀ n : Fin 8,
    3 / 2 ≤ fibRatio (n.val + 3) ∧
    fibRatio (n.val + 3) ≤ 5 / 3 := by native_decide

/-! ## 6. Karamata's regular variation

  f(n) ~ n^α L(n) is regularly varying with index α,
  where L is slowly varying (L(λn)/L(n) → 1). -/

structure RegularlyVaryingData where
  index : ℚ
  slowlyVaryingDesc : String
  radiusOfConvergence : ℚ
deriving DecidableEq

def rvConstantGrowth : RegularlyVaryingData :=
  { index := 0, slowlyVaryingDesc := "1",
    radiusOfConvergence := 1 }
def rvLinearGrowth : RegularlyVaryingData :=
  { index := 1, slowlyVaryingDesc := "1",
    radiusOfConvergence := 1 }
def rvQuadraticGrowth : RegularlyVaryingData :=
  { index := 2, slowlyVaryingDesc := "1/2",
    radiusOfConvergence := 1 }
example : rvConstantGrowth.index = 0 := by native_decide
example : rvLinearGrowth.index = 1 := by native_decide
example : rvQuadraticGrowth.radiusOfConvergence = 1 := by
  native_decide

/-! ## 7. Monotone density theorem

  If aₙ monotone and Σ_{k=0}^n aₖ ~ n^α L(n),
  then aₙ ~ α n^{α−1} L(n).
  Example: aₖ = k+1, Σ ~ n²/2, so aₙ ~ n. -/

def quadraticPartialSum (n : ℕ) : ℚ :=
  ((n + 1) * (n + 2) : ℕ) / 2
example : ∀ n : Fin 15,
    quadraticPartialSum n.val =
      partialSum linearSeq n.val := by native_decide

def partialSumRatio (n : ℕ) : ℚ :=
  if n = 0 then 0
  else quadraticPartialSum n / ((n : ℚ) * (n : ℚ))
-- (n+1)(n+2)/(2n²) → 1/2 = 1/Γ(3) as n → ∞
example : partialSumRatio 5   = 21 / 25      := by native_decide
example : partialSumRatio 10  = 33 / 50      := by native_decide
example : partialSumRatio 100 = 5151 / 10000 := by native_decide

end Tauberian
