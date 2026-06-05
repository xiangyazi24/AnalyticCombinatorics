import Mathlib

/-!
# Rooted forests with a specified root set

This file records the functional formulation of rooted labelled forests used in
Flajolet--Sedgewick, Chapter II: a forest rooted at a specified set `R` is a
parent map from non-roots to all vertices whose `step`-orbits are absorbed by
`R`.

The full Cayley--Pollak count is

`# rootedForests R = |R| * n ^ (n - |R| - 1)` for `0 < |R| < n`,

with the separate all-roots case equal to `1`.  The file proves the faithful
definitions, the all-roots and one-non-root cases, the total number of parent
maps, and the Abel/binomial identity that is the algebraic core of the standard
depth-one recurrence proof.
-/

open scoped BigOperators

namespace AnalyticCombinatorics.Ch2.Mappings.ForestCountNS

noncomputable section

/-- The non-root vertices for a specified root set. -/
abbrev NonRoot {n : ℕ} (R : Finset (Fin n)) : Type :=
  {x : Fin n // x ∉ R}

/--
Extend a partial parent map to all vertices by fixing the roots.  Non-roots move
to their chosen parent; roots are absorbing.
-/
def step {n : ℕ} (R : Finset (Fin n)) (g : NonRoot R → Fin n) (y : Fin n) : Fin n :=
  if h : y ∈ R then y else g ⟨y, h⟩

/-- A vertex reaches the root set under the absorbing extension of the parent map. -/
def Reaches {n : ℕ} (R : Finset (Fin n)) (g : NonRoot R → Fin n) (x : Fin n) : Prop :=
  ∃ m : ℕ, (step R g)^[m] x ∈ R

/-- Functional rooted forests with specified root set `R`. -/
abbrev RootedForests {n : ℕ} (R : Finset (Fin n)) : Type :=
  {g : NonRoot R → Fin n // ∀ x : Fin n, Reaches R g x}

/--
The explicit subtype fintype used for forest counts.  `Mathlib` also imports
category-theoretic finite-category instances; pinning this instance keeps the
cardinality statements definitionally stable.
-/
@[reducible] def rootedForestsFintype {n : ℕ} (R : Finset (Fin n)) :
    Fintype (RootedForests R) := by
  classical
  exact Subtype.fintype (fun g : NonRoot R → Fin n => ∀ x : Fin n, Reaches R g x)

@[simp] lemma step_of_mem {n : ℕ} {R : Finset (Fin n)} (g : NonRoot R → Fin n)
    {y : Fin n} (hy : y ∈ R) :
    step R g y = y := by
  simp [step, hy]

@[simp] lemma step_of_notMem {n : ℕ} {R : Finset (Fin n)} (g : NonRoot R → Fin n)
    {y : Fin n} (hy : y ∉ R) :
    step R g y = g ⟨y, hy⟩ := by
  simp [step, hy]

lemma reaches_of_mem {n : ℕ} {R : Finset (Fin n)} (g : NonRoot R → Fin n)
    {x : Fin n} (hx : x ∈ R) :
    Reaches R g x := by
  exact ⟨0, by simpa [Reaches] using hx⟩

/-- The complement of a root set has the expected cardinality. -/
lemma card_nonRoot {n : ℕ} (R : Finset (Fin n)) :
    Fintype.card (NonRoot R) = n - R.card := by
  classical
  unfold NonRoot
  rw [Fintype.card_subtype_compl (fun x : Fin n => x ∈ R)]
  simp [Fintype.card_fin]

/-- Without the reachability condition, there are `n^(n-|R|)` parent maps. -/
theorem card_parentMaps {n : ℕ} (R : Finset (Fin n)) :
    Fintype.card (NonRoot R → Fin n) = n ^ (n - R.card) := by
  classical
  rw [Fintype.card_fun, card_nonRoot R, Fintype.card_fin]

theorem card_parentMaps_of_card {n k : ℕ} (R : Finset (Fin n)) (hk : R.card = k) :
    Fintype.card (NonRoot R → Fin n) = n ^ (n - k) := by
  simp [hk, card_parentMaps R]

/-- If every vertex is a root, the empty parent map is the unique forest. -/
theorem card_rootedForests_all_roots {n : ℕ} (R : Finset (Fin n))
    (hR : R = Finset.univ) :
    @Fintype.card (RootedForests R) (rootedForestsFintype R) = 1 := by
  classical
  refine (@Fintype.card_eq_one_iff (RootedForests R) (rootedForestsFintype R)).mpr ?_
  refine ⟨⟨(fun x => False.elim ?_), ?_⟩, ?_⟩
  · exact x.2 (by simp [hR])
  · intro x
    exact ⟨0, by simp [hR]⟩
  · intro F
    apply Subtype.ext
    funext x
    exact False.elim (x.2 (by simp [hR]))

/-- The `k = n` case, stated by cardinality of the specified root set. -/
theorem card_rootedForests_all_roots_of_card {n : ℕ} (R : Finset (Fin n))
    (hcard : R.card = n) :
    @Fintype.card (RootedForests R) (rootedForestsFintype R) = 1 := by
  classical
  have hR : R = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [Fintype.card_fin] using hcard
  exact card_rootedForests_all_roots R hR

lemma forest_parent_of_unique_nonRoot_mem_roots {n : ℕ} {R : Finset (Fin n)}
    (a : NonRoot R) (ha : ∀ x : NonRoot R, x = a) (F : RootedForests R) :
    F.1 a ∈ R := by
  classical
  by_contra hnot
  have hstep : step R F.1 a.1 = a.1 := by
    simpa [step, a.2] using congrArg Subtype.val (ha ⟨F.1 a, hnot⟩)
  rcases F.2 a.1 with ⟨m, hm⟩
  have hfixed : (step R F.1)^[m] a.1 = a.1 :=
    Function.iterate_fixed hstep m
  exact a.2 (by simpa [hfixed] using hm)

lemma reaches_unique_nonRoot {n : ℕ} {R : Finset (Fin n)}
    (a : NonRoot R) (ha : ∀ x : NonRoot R, x = a) (r : R) :
    ∀ x : Fin n, Reaches R (fun _ : NonRoot R => (r : Fin n)) x := by
  intro x
  by_cases hx : x ∈ R
  · exact reaches_of_mem (fun _ : NonRoot R => (r : Fin n)) hx
  · have hx_eq : (⟨x, hx⟩ : NonRoot R) = a := ha ⟨x, hx⟩
    refine ⟨1, ?_⟩
    simp [step_of_notMem (fun _ : NonRoot R => (r : Fin n)) hx]

/--
If there is exactly one non-root vertex, a forest is determined by the root that
is its parent.
-/
def rootedForestsEquivRootsOfUniqueNonRoot {n : ℕ} {R : Finset (Fin n)}
    (a : NonRoot R) (ha : ∀ x : NonRoot R, x = a) :
    RootedForests R ≃ R where
  toFun F := ⟨F.1 a, forest_parent_of_unique_nonRoot_mem_roots a ha F⟩
  invFun r := ⟨(fun _ : NonRoot R => (r : Fin n)), reaches_unique_nonRoot a ha r⟩
  left_inv F := by
    apply Subtype.ext
    funext x
    have hx : x = a := ha x
    calc
      (fun _ : NonRoot R => F.1 a) x = F.1 a := rfl
      _ = F.1 x := by rw [hx]
  right_inv r := by
    ext
    rfl

/-- The boundary case `|R| + 1 = n`: one non-root, hence `|R|` forests. -/
theorem card_rootedForests_one_nonRoot {n : ℕ} (R : Finset (Fin n))
    (hcard : R.card + 1 = n) :
    @Fintype.card (RootedForests R) (rootedForestsFintype R) = R.card := by
  classical
  have hnonRoot : Fintype.card (NonRoot R) = 1 := by
    rw [card_nonRoot R]
    omega
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hnonRoot
  calc
    @Fintype.card (RootedForests R) (rootedForestsFintype R) = Fintype.card R := by
      exact @Fintype.card_congr (RootedForests R) R (rootedForestsFintype R) inferInstance
        (rootedForestsEquivRootsOfUniqueNonRoot a ha)
    _ = R.card := by
      exact Fintype.card_coe R

/--
The Cayley formula in the one-non-root boundary case.  Here
`n - k - 1 = 0`, so the right hand side is just `k`.
-/
theorem card_rootedForests_one_nonRoot_formula {n k : ℕ} (R : Finset (Fin n))
    (hk : R.card = k) (hcard : k + 1 = n) :
    @Fintype.card (RootedForests R) (rootedForestsFintype R) =
      k * n ^ (n - k - 1) := by
  classical
  have hRcard : R.card + 1 = n := by simpa [hk] using hcard
  have hn_sub : n - k - 1 = 0 := by omega
  calc
    @Fintype.card (RootedForests R) (rootedForestsFintype R) = R.card :=
      card_rootedForests_one_nonRoot R hRcard
    _ = k * n ^ (n - k - 1) := by
      simp [hk, hn_sub]

/--
The reindexed Abel/binomial identity used by the standard depth-one recurrence
for rooted forests.  It is exactly the binomial theorem after factoring out the
initial `k`.
-/
theorem abel_forest_reindexed_identity {m k : ℕ} (hm : 0 < m) :
    (∑ i ∈ Finset.range m,
        (Nat.choose (m - 1) i) * k ^ (i + 1) * m ^ (m - 1 - i)) =
      k * (m + k) ^ (m - 1) := by
  classical
  have hmrange : (m - 1) + 1 = m := Nat.sub_add_cancel hm
  have hbinom :
      (k + m) ^ (m - 1) =
        ∑ i ∈ Finset.range m,
          (Nat.choose (m - 1) i) * k ^ i * m ^ (m - 1 - i) := by
    rw [add_pow]
    simp [hmrange, mul_assoc, mul_comm, mul_left_comm]
  calc
    (∑ i ∈ Finset.range m,
        (Nat.choose (m - 1) i) * k ^ (i + 1) * m ^ (m - 1 - i))
        =
        k * (∑ i ∈ Finset.range m,
          (Nat.choose (m - 1) i) * k ^ i * m ^ (m - 1 - i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Nat.pow_succ']
      ring_nf
    _ = k * (k + m) ^ (m - 1) := by
      rw [hbinom]
    _ = k * (m + k) ^ (m - 1) := by
      rw [Nat.add_comm]

end

end AnalyticCombinatorics.Ch2.Mappings.ForestCountNS
