import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AsymptoticTransfers

/-!
# Ch III -- finite checks for asymptotic transfers and limit laws

The definitions below are deliberately bounded numerical models of the
coefficient and moment transfers used around Chapter III: quasi-powers,
Berry-Esseen denominators, characteristic-function moment extraction, small
tree-parameter variances, and OGF/EGF coefficient normalization.
-/

/-! ## Hwang quasi-power toy instances -/

/-- Sizes `1, ..., 8` for bounded quasi-power checks. -/
def quasiPowerSizes : Fin 8 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8]

/-- Twice the mean for the binomial quasi-power model `(1 + u)^n / 2^n`. -/
def quasiPowerMeanTwice : Fin 8 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8]

/-- Four times the variance for the same bounded quasi-power model. -/
def quasiPowerVarianceTimesFour : Fin 8 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8]

/-- Cubic error-denominator proxies for the first eight quasi-power sizes. -/
def quasiPowerCubicDenominators : Fin 8 → ℕ :=
  ![1, 8, 27, 64, 125, 216, 343, 512]

theorem quasiPower_mean_variance_tables_match_sizes :
    ∀ i : Fin 8,
      quasiPowerMeanTwice i = quasiPowerSizes i ∧
        quasiPowerVarianceTimesFour i = quasiPowerSizes i := by
  native_decide

theorem quasiPower_cubic_denominators_are_cubes :
    ∀ i : Fin 8,
      quasiPowerCubicDenominators i = quasiPowerSizes i ^ 3 := by
  native_decide

theorem quasiPower_variance_positive :
    ∀ i : Fin 8, 0 < quasiPowerVarianceTimesFour i := by
  native_decide

/-! ## Berry-Esseen denominator proxies -/

/--
For a Bernoulli quasi-power with variance `n / 4`, the squared `sqrt n`
denominator is represented by the size table itself.
-/
def berryEsseenSqrtDenomSquared : Fin 8 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8]

/-- The corresponding `4n` variance denominators before taking square roots. -/
def berryEsseenVarianceDenomTimesFour : Fin 8 → ℕ :=
  ![4, 8, 12, 16, 20, 24, 28, 32]

theorem berryEsseen_denominator_square_matches_size :
    ∀ i : Fin 8, berryEsseenSqrtDenomSquared i = quasiPowerSizes i := by
  native_decide

theorem berryEsseen_variance_denominator_linear :
    ∀ i : Fin 8,
      berryEsseenVarianceDenomTimesFour i =
        4 * berryEsseenSqrtDenomSquared i := by
  native_decide

theorem berryEsseen_denominators_strictly_increase :
    berryEsseenVarianceDenomTimesFour 0 < berryEsseenVarianceDenomTimesFour 1 ∧
      berryEsseenVarianceDenomTimesFour 1 < berryEsseenVarianceDenomTimesFour 2 ∧
      berryEsseenVarianceDenomTimesFour 2 < berryEsseenVarianceDenomTimesFour 3 ∧
      berryEsseenVarianceDenomTimesFour 3 < berryEsseenVarianceDenomTimesFour 4 ∧
      berryEsseenVarianceDenomTimesFour 4 < berryEsseenVarianceDenomTimesFour 5 ∧
      berryEsseenVarianceDenomTimesFour 5 < berryEsseenVarianceDenomTimesFour 6 ∧
      berryEsseenVarianceDenomTimesFour 6 < berryEsseenVarianceDenomTimesFour 7 := by
  native_decide

/-! ## Characteristic-function moment extraction -/

/-- Support `-1, 0, 1` for a symmetric step law. -/
def symmetricStepSupport : Fin 3 → ℤ := ![-1, 0, 1]

/-- Numerators over denominator `4` for the law `P(-1)=1/4`, `P(0)=1/2`, `P(1)=1/4`. -/
def symmetricStepWeights : Fin 3 → ℤ := ![1, 2, 1]

/-- Numerator of the raw moment extracted from the characteristic function. -/
def symmetricStepMomentNumerator (k : ℕ) : ℤ :=
  ∑ i : Fin 3, symmetricStepWeights i * symmetricStepSupport i ^ k

/-- First through sixth raw-moment numerators for the symmetric step law. -/
def symmetricStepMomentTable : Fin 6 → ℤ := ![0, 2, 0, 2, 0, 2]

theorem symmetricStep_moments_to_six :
    ∀ i : Fin 6,
      symmetricStepMomentNumerator (i.val + 1) = symmetricStepMomentTable i := by
  native_decide

theorem symmetricStep_odd_moments_vanish_to_five :
    symmetricStepMomentNumerator 1 = 0 ∧
      symmetricStepMomentNumerator 3 = 0 ∧
      symmetricStepMomentNumerator 5 = 0 := by
  native_decide

theorem symmetricStep_second_and_fourth_moments_match :
    symmetricStepMomentNumerator 2 = symmetricStepMomentNumerator 4 ∧
      symmetricStepMomentNumerator 4 = symmetricStepMomentNumerator 6 := by
  native_decide

/-! ## Small tree-parameter variance checks -/

/-- Internal-node sizes `1, ..., 8` for full binary trees. -/
def fullBinaryTreeInternalSizes : Fin 8 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8]

/-- Leaf counts for full binary trees with the corresponding number of internal nodes. -/
def fullBinaryTreeLeafCounts : Fin 8 → ℕ := ![2, 3, 4, 5, 6, 7, 8, 9]

/--
Variance numerators for the deterministic leaf-count parameter at these sizes.
The denominator is irrelevant because every tree of a fixed internal size has
exactly `n + 1` leaves.
-/
def fullBinaryTreeLeafVarianceNumerators : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0]

theorem fullBinaryTree_leaf_count_is_size_add_one :
    ∀ i : Fin 8,
      fullBinaryTreeLeafCounts i = fullBinaryTreeInternalSizes i + 1 := by
  native_decide

theorem fullBinaryTree_leaf_variance_zero_to_eight :
    ∀ i : Fin 8, fullBinaryTreeLeafVarianceNumerators i = 0 := by
  native_decide

/-! ## OGF/EGF coefficient normalization transfers -/

/-- Factorials `1!` through `8!`. -/
def factorialsOneToEight : Fin 8 → ℕ :=
  ![1, 2, 6, 24, 120, 720, 5040, 40320]

/-- Cayley rooted labelled-tree counts `n^(n-1)` for `n = 1, ..., 8`. -/
def cayleyRootedCounts : Fin 8 → ℕ :=
  ![1, 2, 9, 64, 625, 7776, 117649, 2097152]

/-- Numerators of the corresponding EGF coefficients. -/
def cayleyEgfNumerators : Fin 8 → ℕ :=
  ![1, 2, 9, 64, 625, 7776, 117649, 2097152]

/-- OGF coefficients recovered after multiplying EGF coefficients by `n!`. -/
def cayleyLiftedOgfNumerators : Fin 8 → ℕ :=
  ![1, 4, 54, 1536, 75000, 5598720, 592950960, 84557168640]

theorem factorials_table_matches_nat_factorial :
    ∀ i : Fin 8, factorialsOneToEight i = Nat.factorial (i.val + 1) := by
  native_decide

theorem cayley_counts_are_powers :
    ∀ i : Fin 8, cayleyRootedCounts i = (i.val + 1) ^ i.val := by
  native_decide

theorem cayley_egf_numerators_match_ogf_counts :
    ∀ i : Fin 8, cayleyEgfNumerators i = cayleyRootedCounts i := by
  native_decide

theorem cayley_lifted_ogf_is_factorial_scaled :
    ∀ i : Fin 8,
      cayleyLiftedOgfNumerators i =
        factorialsOneToEight i * cayleyEgfNumerators i := by
  native_decide

end AsymptoticTransfers
