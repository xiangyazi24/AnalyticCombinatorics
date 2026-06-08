import AnalyticCombinatorics.Ch8.Partitions.ITERCoupling

/-!
# R7 Fact B via Doeblin: Green-potential occupation lower bound

The window-occupation `∑_{t<M} goodMass t` is bounded **below** by a Green/Poisson potential of the
residual coupling.  ChatGPT R6 correctly flagged that a `D²` submartingale gives the wrong sign for an
occupation lower bound; the right vehicle is a potential `g` on pairs that is a *Poisson subsolution* for
the residual kernel `Kres`:

  `∑_{a,b} Kres(x,y,a,b)·g(a,b) ≥ g(x,y) − 1_GoodW(x,y)`.

Telescoping the Green-weighted residual mass `Ξ t = ∑ Umat t · g` then gives, with `0 ≤ g ≤ B`,

  `g i j − B·umass M ≤ ∑_{t<M} goodMass t`.

This is finite-sum algebra over the banked `Umat` recursion.  It isolates the entire remaining wall to a
single analytic input: a Green potential `g` (the residual rank-difference walk's expected window
local-time before absorption) with `g i j → ∞` for high-rank comparable starts — the recurrence fact,
now packaged as a bounded subsolution rather than a martingale.  Opus-authored (vehicle ChatGPT R6).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

/-- Green-weighted residual mass after `t` steps. -/
def greenMass (g : α → α → ℝ) (t : ℕ) : ℝ :=
  ∑ a, ∑ b, Umat P rnk W i j t a b * g a b

include hPnn hPmass in
/-- **One-step Green drop.** For a Poisson subsolution `g` of the residual kernel, the Green-weighted
mass drops by at most the window mass: `greenMass (t+1) ≥ greenMass t − goodMass t`. -/
lemma greenMass_succ_ge (g : α → α → ℝ)
    (hsub : ∀ x y, g x y - (if GoodW rnk W x y then (1:ℝ) else 0)
        ≤ ∑ a, ∑ b, Kres P rnk W x y a b * g a b)
    (t : ℕ) :
    greenMass P rnk W i j g t - goodMass P rnk W i j t
      ≤ greenMass P rnk W i j g (t + 1) := by
  have e1 : greenMass P rnk W i j g (t + 1)
      = ∑ a, ∑ b, ∑ x, ∑ y, Umat P rnk W i j t x y * Kres P rnk W x y a b * g a b := by
    unfold greenMass
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    simp only [Umat, Finset.sum_mul]
  have hreorder : (∑ a, ∑ b, ∑ x, ∑ y, Umat P rnk W i j t x y * Kres P rnk W x y a b * g a b)
      = ∑ x, ∑ y, ∑ a, ∑ b, Umat P rnk W i j t x y * Kres P rnk W x y a b * g a b := by
    calc ∑ a, ∑ b, ∑ x, ∑ y, Umat P rnk W i j t x y * Kres P rnk W x y a b * g a b
        = ∑ a, ∑ x, ∑ b, ∑ y, Umat P rnk W i j t x y * Kres P rnk W x y a b * g a b := by
          refine Finset.sum_congr rfl (fun a _ => ?_); rw [Finset.sum_comm]
      _ = ∑ x, ∑ a, ∑ b, ∑ y, Umat P rnk W i j t x y * Kres P rnk W x y a b * g a b := by
          rw [Finset.sum_comm]
      _ = ∑ x, ∑ a, ∑ y, ∑ b, Umat P rnk W i j t x y * Kres P rnk W x y a b * g a b := by
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ => ?_))
          rw [Finset.sum_comm]
      _ = ∑ x, ∑ y, ∑ a, ∑ b, Umat P rnk W i j t x y * Kres P rnk W x y a b * g a b := by
          refine Finset.sum_congr rfl (fun x _ => ?_); rw [Finset.sum_comm]
  have hexp : greenMass P rnk W i j g (t + 1)
      = ∑ x, ∑ y, Umat P rnk W i j t x y * (∑ a, ∑ b, Kres P rnk W x y a b * g a b) := by
    rw [e1, hreorder]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hexp]
  have hge : ∑ x, ∑ y, Umat P rnk W i j t x y * (g x y - (if GoodW rnk W x y then (1:ℝ) else 0))
      ≤ ∑ x, ∑ y, Umat P rnk W i j t x y * (∑ a, ∑ b, Kres P rnk W x y a b * g a b) := by
    refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
    exact mul_le_mul_of_nonneg_left (hsub x y) (Umat_nonneg P rnk W hPnn hPmass i j t x y)
  refine le_trans ?_ hge
  -- LHS = greenMass t - goodMass t
  have hsplit : ∑ x, ∑ y, Umat P rnk W i j t x y * (g x y - (if GoodW rnk W x y then (1:ℝ) else 0))
      = greenMass P rnk W i j g t - goodMass P rnk W i j t := by
    unfold greenMass goodMass
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases hg : GoodW rnk W x y
    · rw [if_pos hg, if_pos hg]; ring
    · rw [if_neg hg, if_neg hg]; ring
  rw [hsplit]

/-- The Green-weighted mass at time `0` is the potential at the start pair. -/
lemma greenMass_zero (g : α → α → ℝ) : greenMass P rnk W i j g 0 = g i j := by
  unfold greenMass
  have hpt : ∀ a b, Umat P rnk W i j 0 a b * g a b
      = if a = i ∧ b = j then g i j else 0 := by
    intro a b
    simp only [Umat]
    by_cases h : a = i ∧ b = j
    · obtain ⟨h1, h2⟩ := h
      rw [if_pos ⟨h1, h2⟩, if_pos ⟨h1, h2⟩, h1, h2, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hpt a b))]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro b _ hb; rw [if_neg (by tauto)]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro a _ ha; refine Finset.sum_eq_zero (fun b _ => ?_); rw [if_neg (by tauto)]
  · intro h; exact absurd (Finset.mem_univ i) h

include hPnn hPmass in
/-- **Green telescoping (tight).** For any Poisson subsolution `g`, the cumulative window occupation is
at least the start potential minus the *Green-weighted residual mass at time `M`*.  This is the form
that closes convergence: when `g` is the occupation-before-absorption potential (so `g = 0` on absorbed
pairs), `greenMass M → 0` even though `umass M ↛ 0`, giving `∑ goodMass → g i j`. -/
theorem occupation_ge_green_tight (g : α → α → ℝ)
    (hsub : ∀ x y, g x y - (if GoodW rnk W x y then (1:ℝ) else 0)
        ≤ ∑ a, ∑ b, Kres P rnk W x y a b * g a b) (M : ℕ) :
    g i j - greenMass P rnk W i j g M ≤ ∑ t ∈ Finset.range M, goodMass P rnk W i j t := by
  have htel : greenMass P rnk W i j g 0 - ∑ t ∈ Finset.range M, goodMass P rnk W i j t
      ≤ greenMass P rnk W i j g M := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have hstep := greenMass_succ_ge P rnk W hPnn hPmass i j g hsub M
      linarith [ih, hstep]
  rw [greenMass_zero P rnk W i j g] at htel
  linarith [htel]

include hPnn hPmass in
/-- **Green occupation lower bound (bounded form).** For a Poisson subsolution `g` with `0 ≤ g ≤ B`, the
cumulative window occupation is at least the Green potential at the start minus `B·umass M`. -/
theorem occupation_ge_green (g : α → α → ℝ) (B : ℝ)
    (hsub : ∀ x y, g x y - (if GoodW rnk W x y then (1:ℝ) else 0)
        ≤ ∑ a, ∑ b, Kres P rnk W x y a b * g a b)
    (hgB : ∀ x y, g x y ≤ B) (M : ℕ) :
    g i j - B * umass P rnk W i j M ≤ ∑ t ∈ Finset.range M, goodMass P rnk W i j t := by
  have htight := occupation_ge_green_tight P rnk W hPnn hPmass i j g hsub M
  have hMle : greenMass P rnk W i j g M ≤ B * umass P rnk W i j M := by
    unfold greenMass umass
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun b _ => ?_)
    rw [mul_comm B (Umat P rnk W i j M a b)]
    exact mul_le_mul_of_nonneg_left (hgB a b) (Umat_nonneg P rnk W hPnn hPmass i j M a b)
  linarith [htight, hMle]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
