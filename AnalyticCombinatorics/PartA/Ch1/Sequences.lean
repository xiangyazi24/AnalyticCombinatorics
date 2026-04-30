/-
  Chapter I § I.2 — Sequences (SEQ construction)

  SEQ(B) is the set of all finite sequences of objects from B (including empty).
  If B has OGF B(z) with B(0) = 0, then SEQ(B) has OGF 1/(1 - B(z)),
  equivalently: (1 - B(z)) · SEQ(B)(z) = 1.

  Reference: F&S Proposition I.1.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

open PowerSeries CombinatorialClass

/-- SEQ(B): finite sequences of objects from B, including the empty sequence.
    Requires B(0) = 0 to ensure level sets are finite. -/
def seqClass (B : CombinatorialClass) (hB : B.count 0 = 0) : CombinatorialClass where
  Obj := List B.Obj
  size := fun xs => xs.foldr (fun b acc => B.size b + acc) 0
  finite_level n := by
    -- Local replacement for private level_mem_iff
    have mem_level : ∀ (m : ℕ) (x : B.Obj), x ∈ B.level m ↔ B.size x = m := fun m x => by
      change x ∈ (B.finite_level m).toFinset ↔ B.size x = m
      exact (B.finite_level m).mem_toFinset.trans (by simp)
    -- All elements have size ≥ 1, since hB rules out size-0 objects
    have hpos : ∀ b : B.Obj, 1 ≤ B.size b := by
      intro b
      rcases Nat.eq_zero_or_pos (B.size b) with h0 | h
      · exfalso
        have := Finset.card_pos.mpr ⟨b, (mem_level 0 b).mpr h0⟩
        simp only [count] at hB; omega
      · omega
    -- A list of total size n has length ≤ n
    have hlen_bound : ∀ ys : List B.Obj,
        ys.length ≤ ys.foldr (fun b acc => B.size b + acc) 0 := by
      intro ys
      induction ys with
      | nil => simp
      | cons a t ih =>
        simp only [List.length_cons, List.foldr_cons]
        linarith [hpos a]
    -- Each member of a list of total size n has individual size ≤ that total
    have helem_le : ∀ (ys : List B.Obj) (b : B.Obj), b ∈ ys →
        B.size b ≤ ys.foldr (fun b acc => B.size b + acc) 0 := by
      intro ys
      induction ys with
      | nil => intro _ h; simp_all
      | cons a t ih =>
        intro b hb
        simp only [List.mem_cons, List.foldr_cons] at *
        rcases hb with rfl | hb
        · omega
        · linarith [ih b hb]
    -- Cover: all B.Obj with size < n+1, indexed by Fin (n+1)
    let S : Set B.Obj := ⋃ k : Fin (n + 1), ↑(B.level k.val)
    have hSfin : S.Finite := Set.finite_iUnion (fun k => (B.level k.val).finite_toSet)
    have hmemS : ∀ xs : List B.Obj, xs.foldr (fun b acc => B.size b + acc) 0 = n →
        ∀ b ∈ xs, b ∈ S := by
      intro xs hxs b hb
      simp only [S, Set.mem_iUnion, Finset.mem_coe]
      have hle := helem_le xs b hb
      exact ⟨⟨B.size b, by omega⟩, (mem_level _ b).mpr rfl⟩
    haveI : Finite {x : B.Obj // x ∈ S} := hSfin.to_subtype
    apply Set.Finite.subset
      ((List.finite_length_le {x : B.Obj // x ∈ S} n).image (List.map Subtype.val))
    intro xs hxs
    simp only [Set.mem_image, Set.mem_setOf_eq]
    have hxs' : xs.foldr (fun b acc => B.size b + acc) 0 = n := hxs
    refine ⟨xs.attachWith (· ∈ S) (hmemS xs hxs'), ?_,
            List.attachWith_map_subtype_val (hmemS xs hxs')⟩
    rw [List.length_attachWith]
    have h1 := hlen_bound xs
    omega

/-- Lift a ℕ-valued OGF to ℤ[[z]] where subtraction is available. -/
noncomputable def ogfZ (A : CombinatorialClass) : PowerSeries ℤ :=
  A.ogf.map (algebraMap ℕ ℤ)

namespace seqClass

private lemma mem_level_iff' (C : CombinatorialClass) (m : ℕ) (x : C.Obj) :
    x ∈ C.level m ↔ C.size x = m := by
  change x ∈ (C.finite_level m).toFinset ↔ C.size x = m
  exact (C.finite_level m).mem_toFinset.trans (by simp)

private lemma size_pos {B : CombinatorialClass} (h : B.count 0 = 0) (b : B.Obj) :
    1 ≤ B.size b := by
  rcases Nat.eq_zero_or_pos (B.size b) with h0 | hp
  · exfalso
    have := Finset.card_pos.mpr ⟨b, (mem_level_iff' B 0 b).mpr h0⟩
    simp only [count] at h; omega
  · omega

/-- The empty list is the unique sequence of size 0. -/
lemma count_zero (B : CombinatorialClass) (h : B.count 0 = 0) :
    (seqClass B h).count 0 = 1 := by
  simp only [count]
  rw [Finset.card_eq_one]
  refine ⟨[], ?_⟩
  ext xs
  simp only [Finset.mem_singleton]
  rw [mem_level_iff' (seqClass B h) 0 xs]
  show xs.foldr (fun b acc => B.size b + acc) 0 = 0 ↔ xs = []
  constructor
  · intro hsz
    rcases xs with _ | ⟨a, t⟩
    · rfl
    · exfalso
      simp only [List.foldr_cons] at hsz
      have := size_pos h a
      omega
  · rintro rfl; rfl

/-- For nonempty xs : List B.Obj decomposed b :: ys with size = n+1,
    the pair (B.size b, size ys) is on the antidiagonal of n+1. -/
private lemma cons_on_antidiagonal {B : CombinatorialClass}
    (n : ℕ) (b : B.Obj) (ys : List B.Obj)
    (hbys : (b :: ys).foldr (fun b acc => B.size b + acc) 0 = n + 1) :
    (B.size b, ys.foldr (fun b acc => B.size b + acc) 0) ∈ Finset.antidiagonal (n + 1) := by
  simp only [Finset.mem_antidiagonal]
  simp only [List.foldr_cons] at hbys
  exact hbys

/-- Recursion on counts: count(n+1) = ∑ B.count(k) · count(n+1-k) over antidiagonal. -/
lemma count_succ (B : CombinatorialClass) (h : B.count 0 = 0) (n : ℕ) :
    (seqClass B h).count (n + 1) =
      ∑ p ∈ Finset.antidiagonal (n + 1), B.count p.1 * (seqClass B h).count p.2 := by
  set S := seqClass B h with hS_def
  -- Direct approach: rewrite count as card, build a Finset bijection between
  -- S.level (n+1) and the sigma over antidiagonal of B.level k ×ˢ S.level m,
  -- using (b, ys) ↦ b :: ys.
  let rhsFs : Finset (Σ _ : ℕ × ℕ, B.Obj × List B.Obj) :=
    (Finset.antidiagonal (n + 1)).sigma (fun p => B.level p.1 ×ˢ S.level p.2)
  -- Forward map: rhsFs → S.level (n+1)
  let fwd : (y : Σ _ : ℕ × ℕ, B.Obj × List B.Obj) → y ∈ rhsFs → List B.Obj :=
    fun y _ => y.2.1 :: y.2.2
  -- Helpers to extract pieces of rhsFs membership
  have extract : ∀ y : Σ _ : ℕ × ℕ, B.Obj × List B.Obj, y ∈ rhsFs →
      y.1 ∈ Finset.antidiagonal (n + 1) ∧
      y.2.1 ∈ B.level y.1.1 ∧
      y.2.2 ∈ S.level y.1.2 := by
    intro y hy
    refine ⟨?_, ?_, ?_⟩
    · exact (Finset.mem_sigma.mp hy).1
    · exact (Finset.mem_product.mp (Finset.mem_sigma.mp hy).2).1
    · exact (Finset.mem_product.mp (Finset.mem_sigma.mp hy).2).2
  have hcard : rhsFs.card = (S.level (n + 1)).card := by
    apply Finset.card_bij fwd
    · -- maps to S.level (n+1)
      intro y hy
      obtain ⟨h1, h2, h3⟩ := extract y hy
      have hkm : y.1.1 + y.1.2 = n + 1 := Finset.mem_antidiagonal.mp h1
      have hbsz : B.size y.2.1 = y.1.1 := (mem_level_iff' B y.1.1 y.2.1).mp h2
      have hysz : y.2.2.foldr (fun b acc => B.size b + acc) 0 = y.1.2 :=
        (mem_level_iff' S y.1.2 y.2.2).mp h3
      apply (mem_level_iff' S (n + 1) (y.2.1 :: y.2.2)).mpr
      change B.size y.2.1 + y.2.2.foldr (fun b acc => B.size b + acc) 0 = n + 1
      omega
    · -- injective
      intro y1 hy1 y2 hy2 heq
      obtain ⟨h11, h12, h13⟩ := extract y1 hy1
      obtain ⟨h21, h22, h23⟩ := extract y2 hy2
      have hbsz1 : B.size y1.2.1 = y1.1.1 := (mem_level_iff' B _ _).mp h12
      have hbsz2 : B.size y2.2.1 = y2.1.1 := (mem_level_iff' B _ _).mp h22
      have hysz1 : y1.2.2.foldr (fun b acc => B.size b + acc) 0 = y1.1.2 :=
        (mem_level_iff' S _ _).mp h13
      have hysz2 : y2.2.2.foldr (fun b acc => B.size b + acc) 0 = y2.1.2 :=
        (mem_level_iff' S _ _).mp h23
      change y1.2.1 :: y1.2.2 = y2.2.1 :: y2.2.2 at heq
      have hb : y1.2.1 = y2.2.1 := (List.cons.injEq _ _ _ _).mp heq |>.1
      have hys : y1.2.2 = y2.2.2 := (List.cons.injEq _ _ _ _).mp heq |>.2
      have hk : y1.1.1 = y2.1.1 := by rw [← hbsz1, hb, hbsz2]
      have hm : y1.1.2 = y2.1.2 := by rw [← hysz1, hys, hysz2]
      obtain ⟨⟨k1, m1⟩, b1, ys1⟩ := y1
      obtain ⟨⟨k2, m2⟩, b2, ys2⟩ := y2
      simp_all
    · -- surjective
      intro xs hxs
      have hsz : xs.foldr (fun b acc => B.size b + acc) 0 = n + 1 :=
        (mem_level_iff' S (n + 1) xs).mp hxs
      match xs, hsz with
      | [], hsz => exact absurd hsz (by show (0 : ℕ) ≠ n + 1; omega)
      | b :: ys, hsz =>
        let y : Σ _ : ℕ × ℕ, B.Obj × List B.Obj :=
          ⟨(B.size b, ys.foldr (fun b acc => B.size b + acc) 0), (b, ys)⟩
        refine ⟨y, ?_, rfl⟩
        apply Finset.mem_sigma.mpr
        refine ⟨?_, ?_⟩
        · exact cons_on_antidiagonal n b ys hsz
        · apply Finset.mem_product.mpr
          exact ⟨(mem_level_iff' B _ _).mpr rfl, (mem_level_iff' S _ _).mpr rfl⟩
  rw [show (seqClass B h).count (n + 1) = (S.level (n + 1)).card from rfl, ← hcard,
      Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro p _
  exact Finset.card_product _ _

end seqClass

/-- Recursion at the OGF level: SEQ(z) = 1 + B(z) · SEQ(z) over ℕ[[z]]. -/
lemma seqClass_ogf_recursion (B : CombinatorialClass) (h : B.count 0 = 0) :
    (seqClass B h).ogf = 1 + B.ogf * (seqClass B h).ogf := by
  ext n
  simp only [coeff_ogf, map_add, coeff_one, coeff_mul]
  rcases n with _ | m
  · -- n = 0
    rw [seqClass.count_zero B h]
    simp [h, Finset.antidiagonal_zero]
  · -- n = m + 1
    rw [seqClass.count_succ B h m]
    simp

/-- The OGF of SEQ(B) satisfies (1 - B(z)) · SEQ(z) = 1, provided B(0) = 0. -/
theorem seqClass_ogf_eq (B : CombinatorialClass) (h : B.count 0 = 0) :
    (1 - ogfZ B) * ogfZ (seqClass B h) = 1 := by
  have hN := seqClass_ogf_recursion B h
  have hZ : ogfZ (seqClass B h) = 1 + ogfZ B * ogfZ (seqClass B h) := by
    unfold ogfZ
    have := congrArg (PowerSeries.map (algebraMap ℕ ℤ)) hN
    simpa using this
  calc (1 - ogfZ B) * ogfZ (seqClass B h)
      = ogfZ (seqClass B h) - ogfZ B * ogfZ (seqClass B h) := by ring
    _ = (1 + ogfZ B * ogfZ (seqClass B h)) - ogfZ B * ogfZ (seqClass B h) := by rw [← hZ]
    _ = 1 := by ring

/-!
### Placeholder constructions (F&S Proposition I.2)

MSET(B): multisets — OGF is the Euler product ∏ₙ (1 - zⁿ)^{-bₙ}
PSET(B): powersets — OGF is ∏ₙ (1 + zⁿ)^{bₙ}
CYC(B):  cyclic sequences — OGF is Σₖ φ(k)/k · log(1/(1 - B(zᵏ)))

Full statements require multivariate / EGF machinery; deferred.
-/
