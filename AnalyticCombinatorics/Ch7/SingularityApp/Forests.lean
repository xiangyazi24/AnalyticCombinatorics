import Mathlib
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics
import AnalyticCombinatorics.Ch7.SingularityApp.TreeFunction

/-!
# Rooted labelled forests

A rooted labelled forest on `[n]` is a finite SET of rooted labelled Cayley
trees.  Its EGF is `F(z) = exp(T(z))`, where `T = z exp T` is the tree
function.  The classical Cayley-Prüfer count is

`rootedForest n = (n + 1)^(n - 1)`.

Equivalently, the forest EGF coefficient is the next tree-function
coefficient:

`rootedForest n / n! = treeFunctionCoeff (n + 1)`.

The asymptotic therefore follows from the tree-function Stirling asymptotic,
with the shift contributing the extra factor `exp 1`.
-/

open Filter Asymptotics
open scoped Topology

namespace AnalyticCombinatorics.Ch7.SingularityApp.ForestsNS

/-- Cayley's count of rooted labelled forests on `n` labelled vertices. -/
def rootedForest (n : ℕ) : ℕ :=
  (n + 1) ^ (n - 1)

/-- The coefficient sequence of the rooted labelled forest EGF `exp(T(z))`. -/
noncomputable def rootedForestCoeff (n : ℕ) : ℝ :=
  (rootedForest n : ℝ) / n.factorial

theorem rootedForestCoeff_eq_rootedForest (n : ℕ) :
    rootedForestCoeff n = (rootedForest n : ℝ) / n.factorial := rfl

lemma rootedForestCoeff_eq_treeFunctionCoeff_succ (n : ℕ) :
    rootedForestCoeff n =
      AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff (n + 1) := by
  by_cases hn : n = 0
  · subst n
    norm_num [rootedForestCoeff, rootedForest,
      AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff,
      AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.cayleyRootedTree]
  · have hnp1R : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hpow :
        ((n + 1 : ℕ) : ℝ) ^ n =
          ((n + 1 : ℕ) : ℝ) ^ (n - 1) * ((n + 1 : ℕ) : ℝ) := by
      conv_lhs => rw [← Nat.sub_one_add_one hn]
      rw [pow_succ]
      rw [Nat.sub_one_add_one hn]
    unfold rootedForestCoeff rootedForest
    unfold AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff
    unfold AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.cayleyRootedTree
    rw [show n + 1 - 1 = n by omega]
    rw [show (n + 1).factorial = (n + 1) * n.factorial by
      exact Nat.factorial_succ n]
    norm_num [Nat.cast_mul]
    have hpow' :
        ((n : ℝ) + 1) ^ n =
          ((n : ℝ) + 1) ^ (n - 1) * ((n : ℝ) + 1) := by
      simpa using hpow
    rw [hpow']
    field_simp [hnp1R]

lemma natCast_succ_isEquivalent_self :
    (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) ~[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  have hbase :
      (fun n : ℕ => (n : ℝ)) ~[atTop]
        (fun n : ℕ => (n : ℝ) + 1) := by
    apply isEquivalent_of_tendsto_one
    simpa using tendsto_natCast_div_add_atTop (1 : ℝ)
  have hsucc :
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) =ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) + 1) :=
    Eventually.of_forall fun n => by norm_num
  exact hsucc.trans_isEquivalent hbase.symm

lemma natCast_succ_rpow_three_halves_isEquivalent_self :
    (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))) ~[atTop]
      (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))) := by
  exact natCast_succ_isEquivalent_self.rpow (by intro n; positivity)

lemma forest_shifted_tree_scale_isEquivalent :
    (fun n : ℕ =>
        Real.exp (((n + 1 : ℕ) : ℝ)) /
          (Real.sqrt (2 * Real.pi) * (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)))) ~[atTop]
      (fun n : ℕ =>
        Real.exp 1 * Real.exp (n : ℝ) /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  have hden :
      (fun n : ℕ =>
          Real.sqrt (2 * Real.pi) * (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))) ~[atTop]
        (fun n : ℕ =>
          Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ))) := by
    simpa only [Pi.mul_apply] using
      (Asymptotics.IsEquivalent.refl
        (l := atTop) (u := fun _ : ℕ => Real.sqrt (2 * Real.pi))).mul
        natCast_succ_rpow_three_halves_isEquivalent_self
  have hraw :
      (fun n : ℕ =>
          Real.exp (((n + 1 : ℕ) : ℝ)) /
            (Real.sqrt (2 * Real.pi) * (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)))) ~[atTop]
        (fun n : ℕ =>
          Real.exp (((n + 1 : ℕ) : ℝ)) /
            (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
    simpa only [Pi.div_apply] using
      (Asymptotics.IsEquivalent.refl
        (l := atTop) (u := fun n : ℕ => Real.exp (((n + 1 : ℕ) : ℝ)))).div hden
  exact hraw.trans_eventuallyEq (Eventually.of_forall fun n => by
    dsimp
    rw [show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by norm_num]
    rw [Real.exp_add]
    ring)

theorem rootedForestCoeff_isEquivalent :
    (fun n : ℕ => rootedForestCoeff n) ~[atTop]
      (fun n : ℕ =>
        Real.exp 1 * Real.exp (n : ℝ) /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  have hbridge :
      (fun n : ℕ => rootedForestCoeff n) =ᶠ[atTop]
        (fun n : ℕ =>
          AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff (n + 1)) :=
    Eventually.of_forall rootedForestCoeff_eq_treeFunctionCoeff_succ
  have htree :=
    Asymptotics.IsEquivalent.comp_tendsto
      AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff_isEquivalent
      (tendsto_add_atTop_nat 1)
  have htree' :
      (fun n : ℕ =>
          AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff (n + 1)) ~[atTop]
        (fun n : ℕ =>
          Real.exp (((n + 1 : ℕ) : ℝ)) /
            (Real.sqrt (2 * Real.pi) * (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)))) := by
    simpa [Function.comp_def] using htree
  exact hbridge.trans_isEquivalent
    (htree'.trans forest_shifted_tree_scale_isEquivalent)

theorem rootedForest_over_factorial_isEquivalent :
    (fun n : ℕ => (rootedForest n : ℝ) / n.factorial) ~[atTop]
      (fun n : ℕ =>
        Real.exp 1 * Real.exp (n : ℝ) /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  simpa [rootedForestCoeff] using rootedForestCoeff_isEquivalent

lemma forest_asymptotic_exp_add_scale_eq (n : ℕ) :
    Real.exp 1 * Real.exp (n : ℝ) /
        (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ))) =
      Real.exp ((n : ℝ) + 1) /
        (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ))) := by
  rw [Real.exp_add]
  ring

theorem rootedForest_over_factorial_isEquivalent_exp_add :
    (fun n : ℕ => (rootedForest n : ℝ) / n.factorial) ~[atTop]
      (fun n : ℕ =>
        Real.exp ((n : ℝ) + 1) /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  exact rootedForest_over_factorial_isEquivalent.trans_eventuallyEq
    (Eventually.of_forall fun n => by
      dsimp
      rw [forest_asymptotic_exp_add_scale_eq n])

example : rootedForest 0 = 1 := by
  norm_num [rootedForest]

example : rootedForest 1 = 1 := by
  norm_num [rootedForest]

example : rootedForest 2 = 3 := by
  norm_num [rootedForest]

example : rootedForest 3 = 16 := by
  norm_num [rootedForest]

example : rootedForest 4 = 125 := by
  norm_num [rootedForest]

example : rootedForestCoeff 1 = 1 := by
  norm_num [rootedForestCoeff, rootedForest]

example : rootedForestCoeff 2 = (3 / 2 : ℝ) := by
  norm_num [rootedForestCoeff, rootedForest]

example : rootedForestCoeff 3 = (8 / 3 : ℝ) := by
  norm_num [rootedForestCoeff, rootedForest]

example : rootedForestCoeff 4 = (125 / 24 : ℝ) := by
  norm_num [rootedForestCoeff, rootedForest]

example : rootedForestCoeff 5 = (54 / 5 : ℝ) := by
  norm_num [rootedForestCoeff, rootedForest]

def forestPiFloat : Float :=
  3.141592653589793

def rootedForestCoeffFloat (n : ℕ) : Float :=
  (n.toFloat + 1.0) ^ (n - 1).toFloat / n.factorial.toFloat

def rootedForestAsymptoticFloat (n : ℕ) : Float :=
  Float.exp 1.0 * Float.exp n.toFloat /
    (Float.sqrt (2.0 * forestPiFloat) * Float.pow n.toFloat 1.5)

def rootedForestAsymptoticRatio (n : ℕ) : Float :=
  rootedForestCoeffFloat n / rootedForestAsymptoticFloat n

#eval [1, 2, 3, 4, 5, 10, 25, 50].map fun n =>
  (n, rootedForestCoeffFloat n, rootedForestAsymptoticFloat n, rootedForestAsymptoticRatio n)

end AnalyticCombinatorics.Ch7.SingularityApp.ForestsNS
