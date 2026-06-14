import Mathlib
import AnalyticCombinatorics.Ch1.OGF.Defs
import AnalyticCombinatorics.Ch1.Lagrange.ImplicitSeries
import AnalyticCombinatorics.Ch1.Lagrange.Applications
import AnalyticCombinatorics.Ch2.EGF.Defs
import AnalyticCombinatorics.Ch2.EGF.LabelledSet
import AnalyticCombinatorics.Ch2.EGF.LabelledSetExp
import AnalyticCombinatorics.Ch2.EGF.LabelledSetOde
import AnalyticCombinatorics.Ch7.SingularityApp.TreeFunction

/-!
# Rooted labelled trees as a recursive species, and Cayley's formula via Lagrange

We define a genuine recursive *rooted labelled tree* species object

  `RootedLTree n = root label + SET(rooted subtrees on a partition of the rest)`

and show its EGF satisfies `T = X · exp(T)`. By `implicitSeries_unique` and the
banked Lagrange coefficient `coeff_implicitSeries_exp`, the count is `n^{n-1}`,
matching the banked `cayleyRootedTree` (for `0 < n`).

This is the faithful species route to Cayley's coefficient — no Prüfer code.
-/

noncomputable section

open AnalyticCombinatorics.Ch1
open PowerSeries
open scoped BigOperators

namespace AnalyticCombinatorics.Ch7.SingularityApp.RootedLTreeNS

/-- A labelled rooted tree on `n` labels, in recursive species form: a root
label plus a labelled SET of rooted subtrees on the remaining labels. -/
inductive RootedLTree : ℕ → Type
  | node {n : ℕ}
      (r : Fin n)
      (P : Finpartition (Finset.univ : Finset {x : Fin n // x ≠ r}))
      (child : ∀ B : P.parts, RootedLTree B.val.card) :
      RootedLTree n

/-! ## The recursive Fintype (the one real engineering lemma) -/

/-- `RootedLTree 0` is empty: there is no root in `Fin 0`. -/
def rootedLTreeZeroEquiv : RootedLTree 0 ≃ Empty where
  toFun t := by cases t with | node r P child => exact Fin.elim0 r
  invFun e := e.elim
  left_inv t := by cases t with | node r P child => exact Fin.elim0 r
  right_inv e := e.elim

/-- One-constructor decomposition equivalence for the successor case. -/
def rootedLTreeSuccEquiv (n : ℕ) :
    RootedLTree (n + 1) ≃
      Σ r : Fin (n + 1),
        Σ P : Finpartition (Finset.univ : Finset {x : Fin (n + 1) // x ≠ r}),
          ∀ B : P.parts, RootedLTree B.val.card where
  toFun t := by cases t with | node r P child => exact ⟨r, P, child⟩
  invFun x := RootedLTree.node x.1 x.2.1 x.2.2
  left_inv t := by cases t with | node r P child => rfl
  right_inv x := by rcases x with ⟨r, P, child⟩; rfl

/-- Cardinality of the complement of one point in `Fin (n+1)`. -/
lemma fin_compl_ne_card (n : ℕ) (r : Fin (n + 1)) :
    Fintype.card {x : Fin (n + 1) // x ≠ r} = n := by
  classical
  rw [Fintype.card_subtype]
  have hfilter :
      (Finset.univ.filter (fun x => x ≠ r) : Finset (Fin (n + 1)))
        = Finset.univ.erase r := by
    ext x; by_cases hx : x = r <;> simp [hx]
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ r)]
  simp

/-- Each block of a partition of the (size-`n`) complement has `< n+1` elements. -/
lemma rootedLTree_part_card_lt
    {n : ℕ} {r : Fin (n + 1)}
    (P : Finpartition (Finset.univ : Finset {x : Fin (n + 1) // x ≠ r}))
    (B : P.parts) :
    B.val.card < n + 1 := by
  have hle : B.val.card ≤ Fintype.card {x : Fin (n + 1) // x ≠ r} :=
    B.val.card_le_univ
  rw [fin_compl_ne_card n r] at hle
  exact Nat.lt_succ_of_le hle

/-- The recursive `Fintype`: well-founded recursion on `n`, building the Fintype
of the constructor argument Σ-type from recursive calls on strictly smaller
blocks (`B.val.card < n+1`). -/
instance instFintypeRootedLTree : (n : ℕ) → Fintype (RootedLTree n)
  | 0 => Fintype.ofEquiv Empty rootedLTreeZeroEquiv.symm
  | n + 1 => by
      classical
      haveI :
          ∀ r : Fin (n + 1),
            Fintype
              (Σ P : Finpartition
                (Finset.univ : Finset {x : Fin (n + 1) // x ≠ r}),
                ∀ B : P.parts, RootedLTree B.val.card) := by
        intro r
        haveI :
            ∀ P : Finpartition
              (Finset.univ : Finset {x : Fin (n + 1) // x ≠ r}),
              Fintype (∀ B : P.parts, RootedLTree B.val.card) := by
          intro P
          haveI : ∀ B : P.parts, Fintype (RootedLTree B.val.card) := by
            intro B
            have : B.val.card < n + 1 := rootedLTree_part_card_lt P B
            exact instFintypeRootedLTree B.val.card
          infer_instance
        infer_instance
      exact
        Fintype.ofEquiv
          (Σ r : Fin (n + 1),
            Σ P : Finpartition
              (Finset.univ : Finset {x : Fin (n + 1) // x ≠ r}),
              ∀ B : P.parts, RootedLTree B.val.card)
          (rootedLTreeSuccEquiv n).symm
  termination_by n => n
  decreasing_by exact this

/-! ## The species class and its functional equation -/

/-- The combinatorial class of rooted labelled trees. -/
def rootedLTreeClass : CombClass where
  Obj n := RootedLTree n
  finObj n := instFintypeRootedLTree n

@[simp] lemma rootedLTreeClass_counts (n : ℕ) :
    rootedLTreeClass.counts n = Fintype.card (RootedLTree n) := rfl

@[simp] lemma rootedLTreeClass_counts_zero :
    rootedLTreeClass.counts 0 = 0 := by
  rw [rootedLTreeClass_counts, Fintype.card_eq_zero_iff]
  exact ⟨fun t => rootedLTreeZeroEquiv t |>.elim⟩

/-- Decomposition: a rooted tree on `n+1` labels is a root together with a
labelled SET of `rootedLTreeClass`-structures on the `n` remaining labels. -/
def decompEquiv (n : ℕ) :
    RootedLTree (n + 1) ≃
      Σ r : Fin (n + 1), labelledSetObj rootedLTreeClass {x : Fin (n + 1) // x ≠ r} :=
  rootedLTreeSuccEquiv n

/-- `counts (n+1) = (n+1) · (SET rootedLTreeClass).counts n`. -/
lemma rootedLTreeClass_counts_succ (n : ℕ) :
    rootedLTreeClass.counts (n + 1) =
      (n + 1) * rootedLTreeClass.set.counts n := by
  classical
  rw [rootedLTreeClass_counts, Fintype.card_congr (decompEquiv n), Fintype.card_sigma]
  have hterm : ∀ r : Fin (n + 1),
      Fintype.card (labelledSetObj rootedLTreeClass {x : Fin (n + 1) // x ≠ r})
        = rootedLTreeClass.set.counts n := by
    intro r
    rw [labelledSetObj_card rootedLTreeClass {x : Fin (n + 1) // x ≠ r},
      fin_compl_ne_card n r]
  rw [Finset.sum_congr rfl (fun r _ => hterm r)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The rooted-tree EGF is `X` times the EGF of its SET-of-subtrees. -/
lemma rootedLTreeClass_egf_eq_X_mul_set :
    rootedLTreeClass.egf = X * rootedLTreeClass.set.egf := by
  ext n
  cases n with
  | zero =>
      rw [CombClass.coeff_egf, rootedLTreeClass_counts_zero]
      simp
  | succ m =>
      rw [CombClass.coeff_egf, rootedLTreeClass_counts_succ,
        PowerSeries.coeff_succ_X_mul, CombClass.coeff_egf]
      rw [Nat.factorial_succ]
      push_cast
      have hm : ((m.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
      field_simp

/-- Functional equation: `T = X · exp(T)`. -/
lemma rootedLTreeClass_egf_spec :
    rootedLTreeClass.egf = X * (PowerSeries.exp ℚ).subst rootedLTreeClass.egf := by
  conv_lhs => rw [rootedLTreeClass_egf_eq_X_mul_set]
  rw [CombClass.egf_set rootedLTreeClass rootedLTreeClass_counts_zero]

lemma constantCoeff_rootedLTreeClass_egf :
    constantCoeff rootedLTreeClass.egf = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf,
    rootedLTreeClass_counts_zero]
  simp

/-! ## Cayley's coefficient via Lagrange inversion -/

lemma rootedLTreeClass_egf_eq_implicitSeries_exp :
    rootedLTreeClass.egf =
      AnalyticCombinatorics.Ch1.Lagrange.ImplicitSeries.implicitSeries
        (PowerSeries.exp ℚ) :=
  AnalyticCombinatorics.Ch1.Lagrange.ImplicitSeries.implicitSeries_unique
    (PowerSeries.exp ℚ) rootedLTreeClass.egf
    rootedLTreeClass_egf_spec constantCoeff_rootedLTreeClass_egf

lemma rootedLTreeClass_coeff_eq_cayley (n : ℕ) (hn : 0 < n) :
    coeff n rootedLTreeClass.egf = (n : ℚ) ^ (n - 1) / n.factorial := by
  rw [rootedLTreeClass_egf_eq_implicitSeries_exp]
  exact AnalyticCombinatorics.Ch1.Lagrange.Applications.coeff_implicitSeries_exp n hn

/-- The species count of rooted labelled trees on `n` labels (for `0 < n`) is
`n^{n-1}`. -/
theorem rootedLTreeClass_count_eq_cayley (n : ℕ) (hn : 0 < n) :
    rootedLTreeClass.counts n = n ^ (n - 1) := by
  have h := rootedLTreeClass_coeff_eq_cayley n hn
  rw [CombClass.coeff_egf] at h
  have hfac : ((n.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hmul : (rootedLTreeClass.counts n : ℚ) = (n : ℚ) ^ (n - 1) := by
    field_simp at h
    linarith [h]
  exact_mod_cast hmul

/-! ## Connection to the banked Ch7 `cayleyRootedTree` / `treeFunctionCoeff` -/

/-- The species count matches the banked `cayleyRootedTree` for `0 < n`. -/
theorem rootedLTreeClass_count_eq_cayleyRootedTree (n : ℕ) (hn : 0 < n) :
    rootedLTreeClass.counts n =
      AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.cayleyRootedTree n := by
  rw [rootedLTreeClass_count_eq_cayley n hn,
    AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.cayleyRootedTree]

/-- The banked tree-function coefficient equals `(species count)/n!` for `0 < n`. -/
theorem treeFunctionCoeff_eq_rootedLTreeClass_count (n : ℕ) (hn : 0 < n) :
    AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff n =
      (rootedLTreeClass.counts n : ℝ) / n.factorial := by
  rw [AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff,
    rootedLTreeClass_count_eq_cayleyRootedTree n hn]

#print axioms rootedLTreeClass_count_eq_cayleyRootedTree
#print axioms treeFunctionCoeff_eq_rootedLTreeClass_count

end AnalyticCombinatorics.Ch7.SingularityApp.RootedLTreeNS
