import AnalyticCombinatorics.Ch8.Partitions.ScalarRecSolve

/-!
# R7 Fact B via Doeblin: the deterministic windowed-coupling ITER (finite-sum algebra)

The renewal-alignment overlap bound, built WITHOUT any probabilistic coupling library — purely as
finite-sum recursion over a finite state type `α` with a stochastic kernel `P`.  We track the coalesced
common-minorant mass `ρ_t` and the unmatched pair mass `U_t`; the marginal invariant
`ρ_t z + ∑_y U_t z y = Pⁿ i z` makes `ρ_t` a common minorant of the two `t`-step laws, so
`∑ ρ_t ≤ overlap`.  The unmatched mass contracts: `u_{t+1} ≤ (1−δ) u_t + δ b_t` with `b_t` the unmatched
mass outside the rank window.  Hence

  `overlap(Pᵐ i ·, Pᵐ j ·) ≥ 1 − (1−δ)^m − δ·∑_{t<m} (1−δ)^{m−t−1} b_t`.

The lone analytic input left is the bad-mass bound `b_t ≤ e_t`.  Opus-authored (construction ChatGPT R3).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Overlap (shared mass) of two mass vectors. -/
def overlap (μ ν : α → ℝ) : ℝ := ∑ z, min (μ z) (ν z)

/-- `t`-step law (right matrix power applied to the point mass at the start). -/
def Mpow (P : α → α → ℝ) : ℕ → α → α → ℝ
  | 0 => fun x y => if x = y then 1 else 0
  | t + 1 => fun x y => ∑ z, Mpow P t x z * P z y

variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

/-- Two states are in the rank window. -/
def GoodW (x y : α) : Prop := (Int.natAbs ((rnk x : ℤ) - (rnk y : ℤ))) ≤ W

instance (x y : α) : Decidable (GoodW rnk W x y) := by unfold GoodW; infer_instance

/-- The common part of two rows on the window. -/
def Cpart (x y z : α) : ℝ := if GoodW rnk W x y then min (P x z) (P y z) else 0

/-- Total common mass at a pair. -/
def cmass (x y : α) : ℝ := ∑ z, Cpart P rnk W x y z

/-- Left/right residual rows. -/
def Lres (x y z : α) : ℝ := P x z - Cpart P rnk W x y z
def Rres (x y z : α) : ℝ := P y z - Cpart P rnk W x y z

/-- Residual product coupling kernel. -/
def Kres (x y a b : α) : ℝ :=
  if cmass P rnk W x y < 1 then Lres P rnk W x y a * Rres P rnk W x y b / (1 - cmass P rnk W x y)
  else 0

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

include hPnn in
lemma Cpart_nonneg (x y z : α) : 0 ≤ Cpart P rnk W x y z := by
  unfold Cpart; split
  · exact le_min (hPnn x z) (hPnn y z)
  · exact le_refl 0

include hPnn in
lemma Cpart_le_left (x y z : α) : Cpart P rnk W x y z ≤ P x z := by
  unfold Cpart; split
  · exact min_le_left _ _
  · exact hPnn x z

include hPnn in
lemma Cpart_le_right (x y z : α) : Cpart P rnk W x y z ≤ P y z := by
  unfold Cpart; split
  · exact min_le_right _ _
  · exact hPnn y z

include hPnn in
lemma Lres_nonneg (x y z : α) : 0 ≤ Lres P rnk W x y z := by
  unfold Lres; linarith [Cpart_le_left P rnk W hPnn x y z]

include hPnn in
lemma Rres_nonneg (x y z : α) : 0 ≤ Rres P rnk W x y z := by
  unfold Rres; linarith [Cpart_le_right P rnk W hPnn x y z]

include hPnn hPmass in
lemma cmass_le_one (x y : α) : cmass P rnk W x y ≤ 1 := by
  unfold cmass
  calc ∑ z, Cpart P rnk W x y z ≤ ∑ z, P x z :=
        Finset.sum_le_sum (fun z _ => Cpart_le_left P rnk W hPnn x y z)
    _ = 1 := hPmass x

include hPnn in
lemma cmass_nonneg (x y : α) : 0 ≤ cmass P rnk W x y :=
  Finset.sum_nonneg (fun z _ => Cpart_nonneg P rnk W hPnn x y z)

include hPmass in
lemma Lres_sum (x y : α) : ∑ z, Lres P rnk W x y z = 1 - cmass P rnk W x y := by
  unfold Lres cmass
  rw [Finset.sum_sub_distrib, hPmass x]

include hPmass in
lemma Rres_sum (x y : α) : ∑ z, Rres P rnk W x y z = 1 - cmass P rnk W x y := by
  unfold Rres cmass
  rw [Finset.sum_sub_distrib, hPmass y]

include hPnn hPmass in
lemma Kres_nonneg (x y a b : α) : 0 ≤ Kres P rnk W x y a b := by
  unfold Kres; split
  · rename_i h
    exact div_nonneg (mul_nonneg (Lres_nonneg P rnk W hPnn x y a) (Rres_nonneg P rnk W hPnn x y b))
      (by linarith)
  · exact le_refl 0

include hPnn hPmass in
lemma Kres_left_marginal (x y a : α) : ∑ b, Kres P rnk W x y a b = Lres P rnk W x y a := by
  unfold Kres
  by_cases h : cmass P rnk W x y < 1
  · simp only [if_pos h]
    have hne : (1 - cmass P rnk W x y) ≠ 0 := by linarith
    rw [← Finset.sum_div, ← Finset.mul_sum, Rres_sum P rnk W hPmass,
      mul_div_assoc, div_self hne, mul_one]
  · simp only [if_neg h, Finset.sum_const_zero]
    have hc1 : cmass P rnk W x y = 1 := le_antisymm (cmass_le_one P rnk W hPnn hPmass x y) (not_lt.mp h)
    have hL0 : ∑ z, Lres P rnk W x y z = 0 := by rw [Lres_sum P rnk W hPmass, hc1]; ring
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => Lres_nonneg P rnk W hPnn x y z)).mp hL0
    exact (this a (Finset.mem_univ a)).symm

include hPnn hPmass in
lemma Kres_right_marginal (x y b : α) : ∑ a, Kres P rnk W x y a b = Rres P rnk W x y b := by
  unfold Kres
  by_cases h : cmass P rnk W x y < 1
  · simp only [if_pos h]
    have hne : (1 - cmass P rnk W x y) ≠ 0 := by linarith
    rw [← Finset.sum_div, ← Finset.sum_mul, Lres_sum P rnk W hPmass,
      mul_comm, mul_div_assoc, div_self hne, mul_one]
  · simp only [if_neg h, Finset.sum_const_zero]
    have hc1 : cmass P rnk W x y = 1 := le_antisymm (cmass_le_one P rnk W hPnn hPmass x y) (not_lt.mp h)
    have hR0 : ∑ z, Rres P rnk W x y z = 0 := by rw [Rres_sum P rnk W hPmass, hc1]; ring
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => Rres_nonneg P rnk W hPnn x y z)).mp hR0
    exact (this b (Finset.mem_univ b)).symm

variable (i j : α)

/-- Unmatched pair mass after `t` steps (initialised at the pair `(i,j)`). -/
def Umat : ℕ → α → α → ℝ
  | 0 => fun a b => if a = i ∧ b = j then 1 else 0
  | t + 1 => fun a b => ∑ x, ∑ y, Umat t x y * Kres P rnk W x y a b

/-- Coalesced common-minorant mass after `t` steps. -/
def rhovec : ℕ → α → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun z => (∑ a, rhovec t a * P a z)
      + ∑ x, ∑ y, Umat P rnk W i j t x y * Cpart P rnk W x y z

include hPnn hPmass in
/-- **Left marginal invariant:** `ρ_t + (U_t's left marginal) = t`-step law from `i`. -/
lemma left_marginal (t : ℕ) (z : α) :
    rhovec P rnk W i j t z + ∑ y, Umat P rnk W i j t z y = Mpow P t i z := by
  induction t generalizing z with
  | zero =>
    simp only [rhovec, Umat, Mpow, zero_add]
    by_cases hz : z = i
    · subst hz; simp
    · rw [if_neg (fun h => hz h.symm)]
      apply Finset.sum_eq_zero
      intro y _
      exact if_neg (fun h => hz h.1)
  | succ t ih =>
    have hU : ∑ y, Umat P rnk W i j (t + 1) z y
        = ∑ x, ∑ y, Umat P rnk W i j t x y * Lres P rnk W x y z := by
      simp only [Umat]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← Finset.mul_sum, Kres_left_marginal P rnk W hPnn hPmass x y z]
    rw [show Mpow P (t + 1) i z = ∑ a, Mpow P t i a * P a z from rfl]
    simp only [rhovec]
    rw [hU, add_assoc]
    rw [show (∑ x, ∑ y, Umat P rnk W i j t x y * Cpart P rnk W x y z)
        + ∑ x, ∑ y, Umat P rnk W i j t x y * Lres P rnk W x y z
        = ∑ x, (∑ y, Umat P rnk W i j t x y) * P x z from ?_]
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← add_mul, ih a]
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← mul_add]
      congr 1
      unfold Lres; ring

include hPnn hPmass in
/-- **Right marginal invariant:** `ρ_t + (U_t's right marginal) = t`-step law from `j`. -/
lemma right_marginal (t : ℕ) (z : α) :
    rhovec P rnk W i j t z + ∑ x, Umat P rnk W i j t x z = Mpow P t j z := by
  induction t generalizing z with
  | zero =>
    simp only [rhovec, Umat, Mpow, zero_add]
    by_cases hz : z = j
    · subst hz; simp
    · rw [if_neg (fun h => hz h.symm)]
      apply Finset.sum_eq_zero
      intro x _
      exact if_neg (fun h => hz h.2)
  | succ t ih =>
    have hU : ∑ x, Umat P rnk W i j (t + 1) x z
        = ∑ x, ∑ y, Umat P rnk W i j t x y * Rres P rnk W x y z := by
      simp only [Umat]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [← Finset.mul_sum, Kres_right_marginal P rnk W hPnn hPmass p q z]
    rw [show Mpow P (t + 1) j z = ∑ a, Mpow P t j a * P a z from rfl]
    simp only [rhovec]
    rw [hU, add_assoc]
    rw [show (∑ x, ∑ y, Umat P rnk W i j t x y * Cpart P rnk W x y z)
        + ∑ x, ∑ y, Umat P rnk W i j t x y * Rres P rnk W x y z
        = ∑ y, (∑ x, Umat P rnk W i j t x y) * P y z from ?_]
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← add_mul, ih a]
    · rw [← Finset.sum_add_distrib]
      rw [show (∑ x, ((∑ y, Umat P rnk W i j t x y * Cpart P rnk W x y z)
          + ∑ y, Umat P rnk W i j t x y * Rres P rnk W x y z))
          = ∑ x, ∑ y, Umat P rnk W i j t x y * P y z from ?_]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_mul]
      · refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← mul_add]
        congr 1
        unfold Rres; ring

/-- Total unmatched mass after `t` steps. -/
def umass (t : ℕ) : ℝ := ∑ x, ∑ y, Umat P rnk W i j t x y

/-- Unmatched mass on pairs inside the rank window. -/
def goodMass (t : ℕ) : ℝ := ∑ x, ∑ y, if GoodW rnk W x y then Umat P rnk W i j t x y else 0

/-- Unmatched mass on pairs outside the rank window. -/
def badMass (t : ℕ) : ℝ := umass P rnk W i j t - goodMass P rnk W i j t

include hPmass in
lemma Mpow_mass (t : ℕ) (x : α) : ∑ z, Mpow P t x z = 1 := by
  induction t generalizing x with
  | zero =>
    simp only [Mpow]
    rw [Finset.sum_ite_eq Finset.univ x (fun _ => (1:ℝ)), if_pos (Finset.mem_univ x)]
  | succ t ih =>
    simp only [Mpow]
    rw [Finset.sum_comm, show (∑ z', ∑ z, Mpow P t x z' * P z' z) = ∑ z', Mpow P t x z' from
      Finset.sum_congr rfl (fun z' _ => by rw [← Finset.mul_sum, hPmass z', mul_one])]
    exact ih x

include hPnn hPmass in
lemma Umat_nonneg (t : ℕ) (a b : α) : 0 ≤ Umat P rnk W i j t a b := by
  induction t generalizing a b with
  | zero => simp only [Umat]; split <;> norm_num
  | succ t ih =>
    simp only [Umat]
    exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
      mul_nonneg (ih x y) (Kres_nonneg P rnk W hPnn hPmass x y a b)))

include hPnn hPmass in
lemma rho_le_left (t : ℕ) (z : α) : rhovec P rnk W i j t z ≤ Mpow P t i z := by
  have h := left_marginal P rnk W hPnn hPmass i j t z
  have h2 : 0 ≤ ∑ y, Umat P rnk W i j t z y :=
    Finset.sum_nonneg (fun y _ => Umat_nonneg P rnk W hPnn hPmass i j t z y)
  linarith

include hPnn hPmass in
lemma rho_le_right (t : ℕ) (z : α) : rhovec P rnk W i j t z ≤ Mpow P t j z := by
  have h := right_marginal P rnk W hPnn hPmass i j t z
  have h2 : 0 ≤ ∑ x, Umat P rnk W i j t x z :=
    Finset.sum_nonneg (fun x _ => Umat_nonneg P rnk W hPnn hPmass i j t x z)
  linarith

include hPnn hPmass in
lemma rho_mass_le_overlap (t : ℕ) :
    ∑ z, rhovec P rnk W i j t z ≤ overlap (Mpow P t i) (Mpow P t j) :=
  Finset.sum_le_sum (fun z _ => le_min (rho_le_left P rnk W hPnn hPmass i j t z)
    (rho_le_right P rnk W hPnn hPmass i j t z))

include hPnn hPmass in
lemma umass_eq (t : ℕ) : umass P rnk W i j t = 1 - ∑ z, rhovec P rnk W i j t z := by
  have hsum : ∑ z, (rhovec P rnk W i j t z + ∑ y, Umat P rnk W i j t z y) = ∑ z, Mpow P t i z :=
    Finset.sum_congr rfl (fun z _ => left_marginal P rnk W hPnn hPmass i j t z)
  rw [Finset.sum_add_distrib, Mpow_mass P hPmass t i] at hsum
  unfold umass
  linarith [hsum]

include hPmass in
lemma rho_succ_sum (t : ℕ) :
    ∑ z, rhovec P rnk W i j (t + 1) z
      = (∑ z, rhovec P rnk W i j t z) + ∑ x, ∑ y, Umat P rnk W i j t x y * cmass P rnk W x y := by
  simp only [rhovec]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => by rw [← Finset.mul_sum, hPmass a, mul_one])
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← Finset.mul_sum]; rfl

include hPnn hPmass in
lemma umass_succ_eq (t : ℕ) :
    umass P rnk W i j (t + 1)
      = umass P rnk W i j t - ∑ x, ∑ y, Umat P rnk W i j t x y * cmass P rnk W x y := by
  rw [umass_eq P rnk W hPnn hPmass i j (t + 1), umass_eq P rnk W hPnn hPmass i j t,
    rho_succ_sum P rnk W hPmass i j t]
  ring

include hPnn hPmass in
lemma umass_core (t : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hminor : ∀ x y, GoodW rnk W x y → δ ≤ cmass P rnk W x y) :
    umass P rnk W i j (t + 1)
      ≤ (1 - δ) * umass P rnk W i j t + δ * badMass P rnk W i j t := by
  rw [umass_succ_eq P rnk W hPnn hPmass i j t]
  have hge : δ * goodMass P rnk W i j t
      ≤ ∑ x, ∑ y, Umat P rnk W i j t x y * cmass P rnk W x y := by
    unfold goodMass
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun y _ => ?_)
    by_cases hg : GoodW rnk W x y
    · rw [if_pos hg, mul_comm]
      exact mul_le_mul_of_nonneg_left (hminor x y hg) (Umat_nonneg P rnk W hPnn hPmass i j t x y)
    · rw [if_neg hg, mul_zero]
      exact mul_nonneg (Umat_nonneg P rnk W hPnn hPmass i j t x y) (cmass_nonneg P rnk W hPnn x y)
  unfold badMass
  linarith [hge]

include hPnn hPmass in
/-- **The ITER window-overlap bound.** -/
lemma iter_window_overlap (m : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hminor : ∀ x y, GoodW rnk W x y → δ ≤ cmass P rnk W x y)
    (e : ℕ → ℝ) (hbad : ∀ t, badMass P rnk W i j t ≤ e t) :
    1 - (1 - δ) ^ m - δ * ∑ t ∈ Finset.range m, (1 - δ) ^ (m - (t + 1)) * e t
      ≤ overlap (Mpow P m i) (Mpow P m j) := by
  have hu0 : umass P rnk W i j 0 = 1 := by
    unfold umass
    have hx : ∀ x, ∑ y, Umat P rnk W i j 0 x y = if x = i then (1:ℝ) else 0 := by
      intro x; simp only [Umat]; by_cases hx : x = i <;> simp [hx]
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_ite_eq' Finset.univ i (fun _ => (1:ℝ)),
      if_pos (Finset.mem_univ i)]
  have hrec : ∀ t, umass P rnk W i j (t + 1) ≤ (1 - δ) * umass P rnk W i j t + δ * e t := by
    intro t
    have hc := umass_core P rnk W hPnn hPmass i j t δ hδ0 hminor
    nlinarith [hc, hbad t, hδ0]
  have hsolve := scalar_rec_solve (q := 1 - δ) (δ := δ) (u := umass P rnk W i j) (e := e)
    (by linarith) hrec m
  rw [hu0, mul_one] at hsolve
  have hov : ∑ z, rhovec P rnk W i j m z ≤ overlap (Mpow P m i) (Mpow P m j) :=
    rho_mass_le_overlap P rnk W hPnn hPmass i j m
  have heq : umass P rnk W i j m = 1 - ∑ z, rhovec P rnk W i j m z :=
    umass_eq P rnk W hPnn hPmass i j m
  linarith [hov, hsolve, heq]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
