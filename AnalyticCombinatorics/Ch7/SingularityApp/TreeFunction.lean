import Mathlib
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Cayley tree-function coefficient asymptotic

The tree function

`T(z) = sum_{n >= 1} n^(n-1) z^n / n!`

has coefficients given exactly by Cayley's rooted labelled tree count.  This
file proves the coefficient asymptotic directly from Stirling's formula:

`n^(n-1) / n! ~ exp n / (sqrt (2*pi) * n^(3/2))`.

The exponent is `3/2`, not `5/2`: Stirling contributes
`1 / sqrt(2*pi*n)` and the quotient `n^(n-1) / n^n` contributes one more
factor `1/n`.
-/

open Filter Asymptotics
open scoped Topology

namespace AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

/-- Cayley's count of rooted labelled trees on `n` labelled vertices. -/
def cayleyRootedTree (n : ℕ) : ℕ :=
  n ^ (n - 1)

/-- The coefficient sequence of the rooted labelled tree EGF. -/
noncomputable def treeFunctionCoeff (n : ℕ) : ℝ :=
  (cayleyRootedTree n : ℝ) / n.factorial

/-- The Stirling scale used by Mathlib's Stirling theorem. -/
noncomputable def treeStirlingScale (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) * Real.pi) * (((n : ℝ) / Real.exp 1) ^ n)

lemma factorial_isEquivalent_treeStirlingScale :
    (fun n : ℕ => (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => treeStirlingScale n) := by
  simpa [treeStirlingScale] using Stirling.factorial_isEquivalent_stirling

lemma cayleyRootedTree_cast (n : ℕ) :
    (cayleyRootedTree n : ℝ) = (n : ℝ) ^ (n - 1) := by
  simp [cayleyRootedTree]

theorem treeFunctionCoeff_eq_cayley (n : ℕ) :
    treeFunctionCoeff n = (cayleyRootedTree n : ℝ) / n.factorial := rfl

lemma treeFunctionCoeff_isEquivalent_treeStirlingScale :
    (fun n : ℕ => treeFunctionCoeff n) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ (n - 1) / treeStirlingScale n) := by
  have hbridge :
      (fun n : ℕ => treeFunctionCoeff n) =ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) ^ (n - 1) / (n.factorial : ℝ)) :=
    Eventually.of_forall fun n => by
      simp [treeFunctionCoeff, cayleyRootedTree_cast]
  have hdiv :
      (fun n : ℕ => (n : ℝ) ^ (n - 1) / (n.factorial : ℝ)) ~[atTop]
        (fun n : ℕ => (n : ℝ) ^ (n - 1) / treeStirlingScale n) := by
    simpa only [Pi.div_apply] using
      (Asymptotics.IsEquivalent.refl
        (l := atTop) (u := fun n : ℕ => (n : ℝ) ^ (n - 1))).div
          factorial_isEquivalent_treeStirlingScale
  exact hbridge.trans_isEquivalent hdiv

lemma rpow_three_halves_mul_nat_real (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  nth_rw 2 [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnpos]
  norm_num

lemma sqrt_two_pi_mul_nat_eq_sqrt_two_pi_mul_rpow_real (n : ℕ) (hn : n ≠ 0) :
    Real.sqrt (2 * (n : ℝ) * Real.pi) * (n : ℝ) =
      Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)) := by
  rw [show 2 * (n : ℝ) * Real.pi = (2 * Real.pi) * (n : ℝ) by ring]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [mul_assoc, rpow_three_halves_mul_nat_real n hn]

lemma treeStirlingScale_simplified (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) ^ (n - 1) / treeStirlingScale n =
      (Real.exp 1) ^ n /
        (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ))) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hE : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have hnpow : (n : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hnR
  have hEpow : (Real.exp 1) ^ n ≠ 0 := pow_ne_zero _ hE
  have hsqrt : Real.sqrt (2 * (n : ℝ) * Real.pi) ≠ 0 := by positivity
  have hpow :
      (n : ℝ) ^ n = (n : ℝ) ^ (n - 1) * (n : ℝ) := by
    conv_lhs => rw [← Nat.sub_one_add_one hn]
    rw [pow_succ]
    rw [Nat.sub_one_add_one hn]
  unfold treeStirlingScale
  rw [div_pow, hpow]
  rw [show
      (n : ℝ) ^ (n - 1) /
          (Real.sqrt (2 * (n : ℝ) * Real.pi) *
            (((n : ℝ) ^ (n - 1) * (n : ℝ)) / (Real.exp 1) ^ n)) =
        (Real.exp 1) ^ n /
          (Real.sqrt (2 * (n : ℝ) * Real.pi) * (n : ℝ)) by
        field_simp [hnpow, hEpow, hnR, hsqrt]]
  rw [sqrt_two_pi_mul_nat_eq_sqrt_two_pi_mul_rpow_real n hn]

theorem treeFunctionCoeff_isEquivalent_exp_one_pow :
    (fun n : ℕ => treeFunctionCoeff n) ~[atTop]
      (fun n : ℕ =>
        (Real.exp 1) ^ n /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  exact treeFunctionCoeff_isEquivalent_treeStirlingScale.trans_eventuallyEq
    ((eventually_ne_atTop 0).mono fun n hn => by
      dsimp
      rw [treeStirlingScale_simplified n hn])

lemma exp_one_pow_nat_eq_exp_nat (n : ℕ) :
    (Real.exp 1) ^ n = Real.exp (n : ℝ) := by
  simp [← Real.exp_nat_mul]

/--
The tree-function coefficient asymptotic.  Since
`treeFunctionCoeff n = n^(n-1)/n!`, Stirling gives the leading term
`exp n / (sqrt(2*pi) * n^(3/2))`.
-/
theorem treeFunctionCoeff_isEquivalent :
    (fun n : ℕ => treeFunctionCoeff n) ~[atTop]
      (fun n : ℕ =>
        Real.exp (n : ℝ) /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  exact treeFunctionCoeff_isEquivalent_exp_one_pow.trans_eventuallyEq
    (Eventually.of_forall fun n => by
      dsimp
      rw [exp_one_pow_nat_eq_exp_nat n])

theorem cayleyRootedTree_over_factorial_isEquivalent :
    (fun n : ℕ => (cayleyRootedTree n : ℝ) / n.factorial) ~[atTop]
      (fun n : ℕ =>
        Real.exp (n : ℝ) /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  simpa [treeFunctionCoeff] using treeFunctionCoeff_isEquivalent

example : treeFunctionCoeff 1 = 1 := by
  norm_num [treeFunctionCoeff, cayleyRootedTree]

example : treeFunctionCoeff 2 = 1 := by
  norm_num [treeFunctionCoeff, cayleyRootedTree]

example : treeFunctionCoeff 3 = (3 / 2 : ℝ) := by
  norm_num [treeFunctionCoeff, cayleyRootedTree]

example : treeFunctionCoeff 4 = (8 / 3 : ℝ) := by
  norm_num [treeFunctionCoeff, cayleyRootedTree]

example : treeFunctionCoeff 5 = (125 / 24 : ℝ) := by
  norm_num [treeFunctionCoeff, cayleyRootedTree]

def piFloat : Float :=
  3.141592653589793

def cayleyCoeffFloat (n : ℕ) : Float :=
  n.toFloat ^ (n - 1).toFloat / n.factorial.toFloat

def cayleyAsymptoticFloat (n : ℕ) : Float :=
  Float.exp n.toFloat /
    (Float.sqrt (2.0 * piFloat) * Float.pow n.toFloat 1.5)

def cayleyAsymptoticRatio (n : ℕ) : Float :=
  cayleyCoeffFloat n / cayleyAsymptoticFloat n

#eval [1, 2, 3, 4, 5].map fun n =>
  (n, cayleyCoeffFloat n, cayleyAsymptoticFloat n, cayleyAsymptoticRatio n)

end AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS
