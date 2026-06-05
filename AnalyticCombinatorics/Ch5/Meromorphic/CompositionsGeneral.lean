import Mathlib
import AnalyticCombinatorics.Ch5.Meromorphic.Transfer
import AnalyticCombinatorics.Ch5.Meromorphic.FibonacciCompositions
import AnalyticCombinatorics.Ch5.Meromorphic.SupercriticalSeqGenuine

/-!
# General finite-part-set compositions

This file develops the finite-alphabet composition model
`1 / (1 - ∑ s ∈ S, z^s)` for a finite nonempty set of positive parts.
-/

open Complex Filter Asymptotics
open scoped BigOperators ComplexOrder ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace CompositionsGeneral

/-- The part polynomial `P_S(x) = ∑_{s∈S} x^s` over a semiring. -/
def partPoly (R : Type*) [Semiring R] (S : Finset ℕ) (x : R) : R :=
  ∑ s ∈ S, x ^ s

/-- Genuine lists of natural-number parts from `S` summing to `n`. -/
def CompList (S : Finset ℕ) (n : ℕ) : Type :=
  {l : List ℕ // (∀ x ∈ l, x ∈ S) ∧ l.sum = n}

/-- Bounded lists over the finite alphabet `S`, used only to build the finite instance for
`CompList`.  The length bound follows from positivity of parts. -/
def BoundedSList (S : Finset ℕ) (n : ℕ) : Type :=
  Σ k : Fin (n + 1), List.Vector {x : ℕ // x ∈ S} k

namespace CompList

variable {S : Finset ℕ} {n : ℕ}

private def toBounded (h0 : 0 ∉ S) (l : CompList S n) : BoundedSList S n := by
  let lS : List {x : ℕ // x ∈ S} :=
    l.1.pmap (fun x hx => ⟨x, l.2.1 x hx⟩) (fun _ hx => hx)
  have hsum : (lS.map (fun x : {x : ℕ // x ∈ S} => x.1)).sum = n := by
    simpa [lS] using l.2.2
  have hpos : ∀ x ∈ l.1, 1 ≤ x := by
    intro x hx
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero fun hx0 => h0 (by simpa [hx0] using l.2.1 x hx))
  have hlen : l.1.length ≤ n := by
    exact (List.length_le_sum_of_one_le l.1 hpos).trans_eq l.2.2
  refine ⟨⟨l.1.length, Nat.lt_succ_of_le hlen⟩, ⟨lS, ?_⟩⟩
  simp [lS]

private def ofBounded (b : BoundedSList S n) : List ℕ :=
  b.2.1.map (fun x : {x : ℕ // x ∈ S} => x.1)

private lemma ofBounded_mem (b : BoundedSList S n) :
    ∀ x ∈ ofBounded (S := S) (n := n) b, x ∈ S := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact y.2

private lemma ofBounded_toBounded (h0 : 0 ∉ S) (l : CompList S n) :
    ofBounded (S := S) (n := n) (toBounded h0 l) = l.1 := by
  dsimp [ofBounded, toBounded]
  simp

private lemma toBounded_injective (h0 : 0 ∉ S) :
    Function.Injective (toBounded (S := S) (n := n) h0) := by
  intro l₁ l₂ h
  apply Subtype.ext
  have hvals := congrArg (ofBounded (S := S) (n := n)) h
  simpa [ofBounded_toBounded h0] using hvals

instance instFintypeBoundedSList (S : Finset ℕ) (n : ℕ) : Fintype (BoundedSList S n) := by
  classical
  letI : Fintype {x : ℕ // x ∈ S} := Finset.Subtype.fintype S
  exact inferInstanceAs (Fintype (Σ k : Fin (n + 1), List.Vector {x : ℕ // x ∈ S} (k : ℕ)))

instance instFintype (S : Finset ℕ) (n : ℕ) (h0 : 0 ∉ S) : Fintype (CompList S n) := by
  classical
  letI : Fintype (BoundedSList S n) := instFintypeBoundedSList S n
  exact Fintype.ofInjective (toBounded (S := S) (n := n) h0) (toBounded_injective h0)

end CompList

/-- Number of ordered compositions of `n` with parts in `S`. -/
def compS (S : Finset ℕ) (h0 : 0 ∉ S) (n : ℕ) : ℕ :=
  letI : Fintype (CompList S n) := CompList.instFintype S n h0
  Fintype.card (CompList S n)

/-- The formal OGF with genuine list-count coefficients. -/
def compSeriesℂ (S : Finset ℕ) (h0 : 0 ∉ S) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (compS S h0 n : ℂ)

/-- The rational OGF `1 / (1 - ∑_{s∈S} z^s)`. -/
def compOGFℂ (S : Finset ℕ) : PowerSeries ℂ :=
  (1 - ∑ s ∈ S, (PowerSeries.X : PowerSeries ℂ) ^ s)⁻¹

@[simp] lemma coeff_compSeriesℂ (S : Finset ℕ) (h0 : 0 ∉ S) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (compSeriesℂ S h0) = (compS S h0 n : ℂ) := by
  simp [compSeriesℂ]

lemma partPoly_zero_of_notMem_zero {R : Type*} [Semiring R] (S : Finset ℕ) (h0 : 0 ∉ S) :
    partPoly R S 0 = 0 := by
  classical
  rw [partPoly]
  refine Finset.sum_eq_zero fun s hs => ?_
  have hs0 : s ≠ 0 := fun h => h0 (by simpa [h] using hs)
  simp [hs0]

lemma partPoly_one (S : Finset ℕ) :
    partPoly ℝ S 1 = (S.card : ℝ) := by
  simp [partPoly]

lemma partPoly_complex_ofReal (S : Finset ℕ) (x : ℝ) :
    partPoly ℂ S (x : ℂ) = (partPoly ℝ S x : ℂ) := by
  simp [partPoly]

lemma partPoly_nonneg {S : Finset ℕ} {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ partPoly ℝ S x := by
  classical
  exact Finset.sum_nonneg fun s _ => pow_nonneg hx s

lemma partPoly_monoOn_nonneg (S : Finset ℕ) :
    MonotoneOn (partPoly ℝ S) (Set.Ici 0) := by
  intro x hx y hy hxy
  dsimp [partPoly]
  exact Finset.sum_le_sum fun s _ => pow_le_pow_left₀ hx hxy s

lemma partPoly_strictMonoOn_nonneg {S : Finset ℕ} (hS : S.Nonempty) (h0 : 0 ∉ S) :
    StrictMonoOn (partPoly ℝ S) (Set.Ici 0) := by
  intro x hx y hy hxy
  classical
  rcases hS with ⟨s, hs⟩
  have hspos : s ≠ 0 := fun hs0 => h0 (by simpa [hs0] using hs)
  have hle_all : ∀ t ∈ S, x ^ t ≤ y ^ t :=
    fun t _ => pow_le_pow_left₀ hx hxy.le t
  have hlt_s : x ^ s < y ^ s :=
    pow_lt_pow_left₀ hxy hx hspos
  dsimp [partPoly]
  exact Finset.sum_lt_sum hle_all ⟨s, hs, hlt_s⟩

lemma partPoly_continuous (S : Finset ℕ) :
    Continuous (partPoly ℝ S) := by
  classical
  unfold partPoly
  fun_prop

lemma list_eq_nil_of_sum_eq_zero_of_one_le (l : List ℕ)
    (hpos : ∀ x ∈ l, 1 ≤ x) (hsum : l.sum = 0) :
    l = [] := by
  cases l with
  | nil => rfl
  | cons x xs =>
      have hx : 1 ≤ x := hpos x (by simp)
      have h : x + xs.sum = 0 := by simpa using hsum
      omega

lemma compList_zero_eq_nil {S : Finset ℕ} (h0 : 0 ∉ S) (l : CompList S 0) :
    l.1 = [] := by
  apply list_eq_nil_of_sum_eq_zero_of_one_le l.1
  · intro x hx
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero fun hx0 => h0 (by simpa [hx0] using l.2.1 x hx))
  · exact l.2.2

def compListZeroEquivPUnit (S : Finset ℕ) (h0 : 0 ∉ S) :
    CompList S 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], by simp⟩
  left_inv l := by
    apply Subtype.ext
    exact (compList_zero_eq_nil h0 l).symm
  right_inv u := by
    cases u
    rfl

theorem compS_zero (S : Finset ℕ) (h0 : 0 ∉ S) :
    compS S h0 0 = 1 := by
  rw [compS]
  letI : Fintype (CompList S 0) := CompList.instFintype S 0 h0
  calc
    Fintype.card (CompList S 0) = Fintype.card Unit :=
      Fintype.card_congr (compListZeroEquivPUnit S h0)
    _ = 1 := by simp

private instance instFintypePartLe (S : Finset ℕ) (n : ℕ) :
    Fintype {s : ℕ // s ∈ S ∧ s ≤ n} := by
  classical
  letI : Fintype {s : ℕ // s ∈ S} := Finset.Subtype.fintype S
  exact Fintype.ofInjective
    (fun s : {s : ℕ // s ∈ S ∧ s ≤ n} => (⟨s.1, s.2.1⟩ : {s : ℕ // s ∈ S}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun t : {s : ℕ // s ∈ S} => t.1) h)

private def firstPartCodomain (S : Finset ℕ) (n : ℕ) : Type :=
  Σ s : {s : ℕ // s ∈ S ∧ s ≤ n + 1}, CompList S (n + 1 - s.1)

private def firstPart (S : Finset ℕ) (n : ℕ) :
    CompList S (n + 1) → firstPartCodomain S n := by
  intro l
  cases l with
  | mk xs hxs =>
    cases xs with
    | nil =>
        have h : (0 : ℕ) = n + 1 := by simpa using hxs.2
        omega
    | cons x xs =>
        have hxS : x ∈ S := hxs.1 x (by simp)
        have hsum_cons : x + xs.sum = n + 1 := by
          simpa using hxs.2
        have hxle : x ≤ n + 1 := by omega
        refine ⟨⟨x, hxS, hxle⟩, ⟨xs, ?_, ?_⟩⟩
        · intro y hy
          exact hxs.1 y (by simp [hy])
        · show xs.sum = n + 1 - x
          omega

private def consPart (S : Finset ℕ) (n : ℕ) :
    firstPartCodomain S n → CompList S (n + 1) := by
  intro a
  rcases a with ⟨s, l⟩
  refine ⟨s.1 :: l.1, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · simpa [hx] using s.2.1
    · exact l.2.1 x hx
  · simp
    have hsle : s.1 ≤ n + 1 := s.2.2
    have hsum : l.1.sum = n + 1 - s.1 := l.2.2
    show s.1 + l.1.sum = n + 1
    omega

private lemma consPart_firstPart (S : Finset ℕ) (n : ℕ) (l : CompList S (n + 1)) :
    consPart S n (firstPart S n l) = l := by
  apply Subtype.ext
  cases l with
  | mk xs hxs =>
    cases xs with
    | nil =>
        have h : (0 : ℕ) = n + 1 := by simpa using hxs.2
        omega
    | cons x xs =>
        rfl

private lemma firstPart_consPart (S : Finset ℕ) (n : ℕ) (a : firstPartCodomain S n) :
    firstPart S n (consPart S n a) = a := by
  rcases a with ⟨⟨x, hxS, hxle⟩, ⟨xs, hmem, hsum⟩⟩
  apply Sigma.ext
  · apply Subtype.ext
    rfl
  · simp [firstPart, consPart]

private def compListSuccEquivSigma (S : Finset ℕ) (n : ℕ) :
    CompList S (n + 1) ≃ firstPartCodomain S n where
  toFun := firstPart S n
  invFun := consPart S n
  left_inv := consPart_firstPart S n
  right_inv := firstPart_consPart S n

theorem compS_succ_eq_sum_subtype (S : Finset ℕ) (h0 : 0 ∉ S) (n : ℕ) :
    compS S h0 (n + 1) =
      ∑ s : {s : ℕ // s ∈ S ∧ s ≤ n + 1}, compS S h0 (n + 1 - s.1) := by
  rw [compS]
  letI : Fintype (CompList S (n + 1)) := CompList.instFintype S (n + 1) h0
  letI : Fintype {s : ℕ // s ∈ S ∧ s ≤ n + 1} := instFintypePartLe S (n + 1)
  letI : ∀ s : {s : ℕ // s ∈ S ∧ s ≤ n + 1},
      Fintype (CompList S (n + 1 - s.1)) :=
    fun s => CompList.instFintype S (n + 1 - s.1) h0
  letI : Fintype (firstPartCodomain S n) := by
    unfold firstPartCodomain
    infer_instance
  have hcard :
      Fintype.card (CompList S (n + 1)) = Fintype.card (firstPartCodomain S n) :=
    Fintype.card_congr (compListSuccEquivSigma S n)
  rw [hcard]
  unfold firstPartCodomain
  change Fintype.card (Sigma (fun s : {s : ℕ // s ∈ S ∧ s ≤ n + 1} =>
      CompList S (n + 1 - s.1))) =
    ∑ s : {s : ℕ // s ∈ S ∧ s ≤ n + 1}, compS S h0 (n + 1 - s.1)
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [compS]

lemma exists_partPoly_eq_one {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ partPoly ℝ S ρ = 1 := by
  classical
  have h0le1 : (0 : ℝ) ≤ 1 := by norm_num
  have hcont : ContinuousOn (partPoly ℝ S) (Set.Icc 0 1) :=
    (partPoly_continuous S).continuousOn
  have hP0 : partPoly ℝ S 0 = 0 :=
    partPoly_zero_of_notMem_zero (R := ℝ) S h0
  have hP1 : partPoly ℝ S 1 = (S.card : ℝ) :=
    partPoly_one S
  have hP0P1 : partPoly ℝ S 0 ≤ partPoly ℝ S 1 := by
    rw [hP0, hP1]
    exact_mod_cast Nat.zero_le S.card
  have hmem : (1 : ℝ) ∈ Set.Icc (partPoly ℝ S 0) (partPoly ℝ S 1) := by
    rw [partPoly_one]
    rw [hP0]
    constructor
    · norm_num
    · have hcardReal : (1 : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hcard)
      simpa using hcardReal
  rcases intermediate_value_Icc h0le1 hcont hmem with ⟨ρ, hρIcc, hρ⟩
  refine ⟨ρ, ?_, ?_, hρ⟩
  · by_contra hnot
    have hρ0 : ρ = 0 := le_antisymm (not_lt.mp hnot) hρIcc.1
    have hzero : partPoly ℝ S ρ = 0 := by
      rw [hρ0]
      exact partPoly_zero_of_notMem_zero (R := ℝ) S h0
    linarith
  · by_contra hnot
    have hρ1 : ρ = 1 := le_antisymm hρIcc.2 (not_lt.mp hnot)
    have hone : partPoly ℝ S ρ = (S.card : ℝ) := by
      rw [hρ1, partPoly_one]
    have hcardReal : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard
    linarith

/-- The positive root as an arbitrary witness.  Theorems below expose its properties. -/
def rhoS (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) : ℝ :=
  Classical.choose (exists_partPoly_eq_one (S := S) hcard h0)

lemma rhoS_pos {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) :
    0 < rhoS S hcard h0 :=
  (Classical.choose_spec (exists_partPoly_eq_one (S := S) hcard h0)).1

lemma rhoS_lt_one {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) :
    rhoS S hcard h0 < 1 :=
  (Classical.choose_spec (exists_partPoly_eq_one (S := S) hcard h0)).2.1

lemma partPoly_rhoS {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) :
    partPoly ℝ S (rhoS S hcard h0) = 1 :=
  (Classical.choose_spec (exists_partPoly_eq_one (S := S) hcard h0)).2.2

theorem partPoly_eq_one_unique_on_nonneg {S : Finset ℕ}
    (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) {x : ℝ} (hx : 0 ≤ x)
    (hxone : partPoly ℝ S x = 1) :
    x = rhoS S hcard h0 := by
  classical
  have hS : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num : 0 < 2) hcard)
  have hstrict := partPoly_strictMonoOn_nonneg (S := S) hS h0
  have hρnonneg : 0 ≤ rhoS S hcard h0 := (rhoS_pos hcard h0).le
  by_cases hlt : x < rhoS S hcard h0
  · have := hstrict hx hρnonneg hlt
    rw [hxone, partPoly_rhoS hcard h0] at this
    exact (lt_irrefl (1 : ℝ) this).elim
  · have hρle : rhoS S hcard h0 ≤ x := le_of_not_gt hlt
    by_cases hgt : rhoS S hcard h0 < x
    · have := hstrict hρnonneg hx hgt
      rw [hxone, partPoly_rhoS hcard h0] at this
      exact (lt_irrefl (1 : ℝ) this).elim
    · exact le_antisymm (le_of_not_gt hgt) hρle

lemma norm_partPoly_le_partPoly_norm (S : Finset ℕ) (z : ℂ) :
    ‖partPoly ℂ S z‖ ≤ partPoly ℝ S ‖z‖ := by
  classical
  calc
    ‖partPoly ℂ S z‖ = ‖∑ s ∈ S, z ^ s‖ := rfl
    _ ≤ ∑ s ∈ S, ‖z ^ s‖ := norm_sum_le S (fun s => z ^ s)
    _ = partPoly ℝ S ‖z‖ := by
      simp [partPoly, norm_pow]

theorem root_norm_eq_rhoS {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    {z : ℂ} (hroot : 1 - partPoly ℂ S z = 0)
    (hzle : ‖z‖ ≤ rhoS S hcard h0) :
    ‖z‖ = rhoS S hcard h0 := by
  classical
  have hP : partPoly ℂ S z = 1 := (sub_eq_zero.mp hroot).symm
  have hnormP : ‖partPoly ℂ S z‖ = 1 := by
    rw [hP, norm_one]
  have hleρ : partPoly ℝ S ‖z‖ ≤ partPoly ℝ S (rhoS S hcard h0) := by
    exact partPoly_monoOn_nonneg S (norm_nonneg z) (rhoS_pos hcard h0).le hzle
  have hle1 : partPoly ℝ S ‖z‖ ≤ 1 := by
    simpa [partPoly_rhoS hcard h0] using hleρ
  have hge1 : 1 ≤ partPoly ℝ S ‖z‖ := by
    rw [← hnormP]
    exact norm_partPoly_le_partPoly_norm S z
  have heq : partPoly ℝ S ‖z‖ = 1 := le_antisymm hle1 hge1
  exact partPoly_eq_one_unique_on_nonneg hcard h0 (norm_nonneg z) heq

lemma complex_eq_of_nonneg (w : ℂ) (hw : 0 ≤ w) :
    w = (‖w‖ : ℝ) := by
  apply Complex.ext
  · exact Complex.re_eq_norm.mpr hw
  · exact (Complex.nonneg_iff.mp hw).2.symm.trans (by simp)

theorem root_powers_nonneg {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    {z : ℂ} (hroot : 1 - partPoly ℂ S z = 0)
    (hzle : ‖z‖ ≤ rhoS S hcard h0) :
    ∀ s ∈ S, 0 ≤ z ^ s := by
  classical
  have hP : partPoly ℂ S z = 1 := (sub_eq_zero.mp hroot).symm
  have hnormz : ‖z‖ = rhoS S hcard h0 :=
    root_norm_eq_rhoS hcard h0 hroot hzle
  have hsum_norm : ∑ s ∈ S, ‖z ^ s‖ = 1 := by
    calc
      ∑ s ∈ S, ‖z ^ s‖ = partPoly ℝ S ‖z‖ := by
        simp [partPoly, norm_pow]
      _ = 1 := by
        rw [hnormz, partPoly_rhoS hcard h0]
  have hsum_re : ∑ s ∈ S, (z ^ s).re = 1 := by
    have hre := congrArg Complex.re hP
    simpa [partPoly] using hre
  have hsum_zero : ∑ s ∈ S, (‖z ^ s‖ - (z ^ s).re) = 0 := by
    rw [Finset.sum_sub_distrib, hsum_norm, hsum_re]
    ring
  have hnonneg : ∀ s ∈ S, 0 ≤ ‖z ^ s‖ - (z ^ s).re := by
    intro s hs
    exact sub_nonneg.mpr (Complex.re_le_norm (z ^ s))
  intro s hs
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero s hs
  have hre_eq : (z ^ s).re = ‖z ^ s‖ := by linarith
  exact Complex.re_eq_norm.mp hre_eq

lemma pow_finset_gcd_eq_one (u : ℂ) (S : Finset ℕ) :
    u ^ (S.gcd id) = 1 ↔ ∀ s ∈ S, u ^ s = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | insert a S ha ih =>
      rw [Finset.gcd_insert]
      change u ^ Nat.gcd (id a) (S.gcd id) = 1 ↔ ∀ s ∈ insert a S, u ^ s = 1
      rw [pow_gcd_eq_one, ih]
      constructor
      · intro h s hs
        rcases Finset.mem_insert.mp hs with rfl | hsS
        · exact h.1
        · exact h.2 s hsS
      · intro h
        constructor
        · exact h a (Finset.mem_insert_self a S)
        · intro s hs
          exact h s (Finset.mem_insert_of_mem hs)

theorem root_eq_rhoS_of_gcd {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    (hgcd : S.gcd id = 1) {z : ℂ}
    (hroot : 1 - partPoly ℂ S z = 0)
    (hzle : ‖z‖ ≤ rhoS S hcard h0) :
    z = (rhoS S hcard h0 : ℂ) := by
  classical
  let ρ : ℝ := rhoS S hcard h0
  have hρpos : 0 < ρ := rhoS_pos hcard h0
  have hρneℂ : ((ρ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hρpos
  have hnormz : ‖z‖ = ρ := by
    simpa [ρ] using root_norm_eq_rhoS hcard h0 hroot hzle
  have hpows_nonneg : ∀ s ∈ S, 0 ≤ z ^ s :=
    root_powers_nonneg hcard h0 hroot hzle
  have hpows_eq : ∀ s ∈ S, z ^ s = ((ρ ^ s : ℝ) : ℂ) := by
    intro s hs
    have hnonneg := hpows_nonneg s hs
    calc
      z ^ s = (‖z ^ s‖ : ℝ) := complex_eq_of_nonneg (z ^ s) hnonneg
      _ = ((ρ ^ s : ℝ) : ℂ) := by
        rw [norm_pow, hnormz]
  let u : ℂ := z / (ρ : ℂ)
  have hu_pows : ∀ s ∈ S, u ^ s = 1 := by
    intro s hs
    have hspos : s ≠ 0 := fun hs0 => h0 (by simpa [hs0] using hs)
    have hρpow_ne : ((ρ : ℂ) ^ s) ≠ 0 := pow_ne_zero s hρneℂ
    calc
      u ^ s = z ^ s / (ρ : ℂ) ^ s := by
        simp [u, div_pow]
      _ = 1 := by
        rw [hpows_eq s hs]
        norm_cast
        field_simp [hρpow_ne]
  have hu_gcd : u ^ (S.gcd id) = 1 :=
    (pow_finset_gcd_eq_one u S).2 hu_pows
  have hu : u = 1 := by
    rw [hgcd] at hu_gcd
    simpa using hu_gcd
  calc
    z = u * (ρ : ℂ) := by
      simp [u, hρneℂ]
    _ = (ρ : ℂ) := by
      rw [hu]
      ring

/-- Formal derivative of the part polynomial at a complex point. -/
def partPolyDerivAt (S : Finset ℕ) (ρ : ℂ) : ℂ :=
  ∑ s ∈ S, (s : ℂ) * ρ ^ (s - 1)

/-- The dominant pole as a complex number. -/
def rhoSℂ (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) : ℂ :=
  (rhoS S hcard h0 : ℂ)

/-- The `c = 1 / P_S'(ρ)` principal-part constant. -/
def residueConstant (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) : ℂ :=
  (partPolyDerivAt S (rhoSℂ S hcard h0))⁻¹

/-- Coefficient asymptotic constant, equal to `1 / (ρ P_S'(ρ))`. -/
def compAsymptoticConstant (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) : ℂ :=
  residueConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹

theorem compS_isEquivalent_of_dominant_decomposition
    (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    (g : PowerSeries ℂ) {R : ℝ}
    (hρR : ‖rhoSℂ S hcard h0‖ < R)
    (hderiv_ne : partPolyDerivAt S (rhoSℂ S hcard h0) ≠ 0)
    (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hdecomp :
      compSeriesℂ S h0 =
        PowerSeries.C (residueConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹) *
          PowerSeries.rescale (rhoSℂ S hcard h0)⁻¹
            (PowerSeries.invUnitsSub (1 : ℂˣ)) + g) :
    (fun n : ℕ => (compS S h0 n : ℂ)) ~[atTop]
      (fun n : ℕ =>
        compAsymptoticConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹ ^ n) := by
  classical
  have hρpos : 0 < ‖rhoSℂ S hcard h0‖ := by
    rw [rhoSℂ]
    rw [Complex.norm_of_nonneg (rhoS_pos hcard h0).le]
    exact rhoS_pos hcard h0
  have hc_ne : residueConstant S hcard h0 ≠ 0 := by
    exact inv_ne_zero hderiv_ne
  have hmain :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (compSeriesℂ S h0)) ~[atTop]
        (fun n : ℕ =>
          residueConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹ ^ (n + 1)) :=
    dominant_simplePole_isEquivalent
      (compSeriesℂ S h0) g
      (ρ := rhoSℂ S hcard h0) (c := residueConstant S hcard h0) (R := R)
      hρpos hρR hc_ne hgR hdecomp
  have hcoeff :
      (fun n : ℕ => (compS S h0 n : ℂ)) =ᶠ[atTop]
        (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (compSeriesℂ S h0)) :=
    Eventually.of_forall fun n => by simp [compSeriesℂ, compS]
  exact (hcoeff.trans_isEquivalent hmain).trans_eventuallyEq
    (Eventually.of_forall fun n => by
      rw [compAsymptoticConstant]
      change residueConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹ ^ (n + 1) =
        residueConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹ *
          (rhoSℂ S hcard h0)⁻¹ ^ n
      rw [pow_succ]
      ring)

end CompositionsGeneral
end Meromorphic
end Ch5
end AnalyticCombinatorics
