import AnalyticCombinatorics.Ch8.Partitions.QVTelescope

/-!
# Variational Green-from-form comparison (renewal route B, Layer-2 Stage 3b)

The finite-dimensional, measure-theory-free heart of the Dirichlet-form Green comparison
(ChatGPT ac2 R10).  For a finite type `ι`, kernel operator `A_K = I − K`, energy form
`Q_K(f) = ⟨A_K f, f⟩`, and a Green operator `G` supplied via the resolvent hypothesis
`A_K (G h) = h`:

* `green_complete_square` — the crux identity `2⟨h,f⟩ − Q_K(f) = ⟨h,u⟩ − Q_K(f−u)` when `A_K u = h`
  (needs `A_K` self-adjoint, i.e. `K` symmetric);
* `green_form_duality_isGreatest` — `⟨h, G h⟩` is the greatest value of `f ↦ 2⟨h,f⟩ − Q_K(f)`
  (`sSup`-free, via `IsGreatest`);
* `green_domination_of_form_le` — **form domination ⟹ Green domination**:
  `Q_K(f) ≤ Λ·Q_R(f)` (∀f) ⟹ `⟨h, G_K h⟩ ≥ Λ⁻¹·⟨h, G_R h⟩`.

The Green operator's existence (Neumann convergence) is kept *separate*: these lemmas only consume the
resolvent identity `hG : ∀ h x, greenA K (G h) x = h x`, so they are pure finite-dim linear algebra.
(The nonreversible/sector generalization — `quadratic_green_compare_sector`, core `2AB−A²≤B²` — and the
cut-flux Hardy SOS are the remaining hard residual; see `DOCTRINE-walls.md` R11/R12.)
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Plain finite-sum dot product on `ι → ℝ`. -/
def dotV (f g : ι → ℝ) : ℝ := ∑ x, f x * g x

/-- Kernel action `K f`. -/
def kerApply (K : ι → ι → ℝ) (f : ι → ℝ) : ι → ℝ := fun x => ∑ y, K x y * f y

/-- The killed/resolvent form operator `A_K = I − K`. -/
def greenA (K : ι → ι → ℝ) (f : ι → ℝ) : ι → ℝ := fun x => f x - kerApply K f x

/-- Dirichlet/resolvent quadratic form `Q_K(f) = ⟨A_K f, f⟩`. -/
def greenQ (K : ι → ι → ℝ) (f : ι → ℝ) : ℝ := dotV (greenA K f) f

/-- Dual functional `2⟨h,f⟩ − Q_K(f)`. -/
def greenDual (K : ι → ι → ℝ) (h f : ι → ℝ) : ℝ := 2 * dotV h f - greenQ K f

lemma dotV_comm (f g : ι → ℝ) : dotV f g = dotV g f := by
  unfold dotV; refine Finset.sum_congr rfl ?_; intro x _; ring

lemma dotV_const_mul_right (c : ℝ) (f g : ι → ℝ) :
    dotV f (fun x => c * g x) = c * dotV f g := by
  unfold dotV
  calc (∑ x, f x * (c * g x)) = ∑ x, c * (f x * g x) := by
        refine Finset.sum_congr rfl ?_; intro x _; ring
    _ = c * ∑ x, f x * g x := by rw [Finset.mul_sum]

lemma dotV_sub_sub (a b c d : ι → ℝ) :
    dotV (fun x => a x - b x) (fun x => c x - d x)
      = dotV a c - dotV a d - dotV b c + dotV b d := by
  unfold dotV
  calc (∑ x, (a x - b x) * (c x - d x))
        = ∑ x, (a x * c x - a x * d x - b x * c x + b x * d x) := by
          refine Finset.sum_congr rfl ?_; intro x _; ring
    _ = (∑ x, a x * c x) - (∑ x, a x * d x) - (∑ x, b x * c x) + (∑ x, b x * d x) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

lemma kerApply_sub (K : ι → ι → ℝ) (f g : ι → ℝ) :
    kerApply K (fun x => f x - g x) = fun x => kerApply K f x - kerApply K g x := by
  funext x; unfold kerApply
  calc (∑ y, K x y * (f y - g y)) = ∑ y, (K x y * f y - K x y * g y) := by
        refine Finset.sum_congr rfl ?_; intro y _; ring
    _ = (∑ y, K x y * f y) - (∑ y, K x y * g y) := by rw [Finset.sum_sub_distrib]

lemma greenA_sub (K : ι → ι → ℝ) (f g : ι → ℝ) :
    greenA K (fun x => f x - g x) = fun x => greenA K f x - greenA K g x := by
  funext x; unfold greenA; rw [kerApply_sub]; ring

lemma kerApply_const_mul (K : ι → ι → ℝ) (c : ℝ) (f : ι → ℝ) :
    kerApply K (fun x => c * f x) = fun x => c * kerApply K f x := by
  funext x; unfold kerApply
  calc (∑ y, K x y * (c * f y)) = ∑ y, c * (K x y * f y) := by
        refine Finset.sum_congr rfl ?_; intro y _; ring
    _ = c * ∑ y, K x y * f y := by rw [Finset.mul_sum]

lemma greenA_const_mul (K : ι → ι → ℝ) (c : ℝ) (f : ι → ℝ) :
    greenA K (fun x => c * f x) = fun x => c * greenA K f x := by
  funext x; unfold greenA; rw [kerApply_const_mul]; ring

lemma greenQ_const_mul (K : ι → ι → ℝ) (c : ℝ) (f : ι → ℝ) :
    greenQ K (fun x => c * f x) = c ^ 2 * greenQ K f := by
  unfold greenQ dotV; rw [greenA_const_mul]
  calc (∑ x, (c * greenA K f x) * (c * f x)) = ∑ x, c ^ 2 * (greenA K f x * f x) := by
        refine Finset.sum_congr rfl ?_; intro x _; ring
    _ = c ^ 2 * ∑ x, greenA K f x * f x := by rw [Finset.mul_sum]

/-- A symmetric kernel gives a self-adjoint `A_K`. -/
lemma greenA_selfAdjoint_of_kernel_symm
    (K : ι → ι → ℝ) (hKsym : ∀ x y, K x y = K y x) :
    ∀ f g : ι → ℝ, dotV (greenA K f) g = dotV f (greenA K g) := by
  intro f g
  unfold dotV greenA kerApply
  calc (∑ x, (f x - ∑ y, K x y * f y) * g x)
        = (∑ x, f x * g x) - ∑ x, (∑ y, K x y * f y) * g x := by
          rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl ?_; intro x _; ring
    _ = (∑ x, f x * g x) - ∑ x, ∑ y, K x y * f y * g x := by
          congr 1; refine Finset.sum_congr rfl ?_; intro x _
          rw [Finset.sum_mul]
    _ = (∑ x, f x * g x) - ∑ y, ∑ x, K x y * f y * g x := by rw [Finset.sum_comm]
    _ = (∑ x, f x * g x) - ∑ y, f y * (∑ x, K y x * g x) := by
          congr 1; refine Finset.sum_congr rfl ?_; intro y _
          calc (∑ x, K x y * f y * g x) = ∑ x, f y * (K y x * g x) := by
                refine Finset.sum_congr rfl ?_; intro x _; rw [hKsym x y]; ring
            _ = f y * ∑ x, K y x * g x := by rw [Finset.mul_sum]
    _ = ∑ x, f x * (g x - ∑ y, K x y * g y) := by
          calc (∑ x, f x * g x) - ∑ y, f y * (∑ x, K y x * g x)
                = (∑ x, f x * g x) - ∑ x, f x * (∑ y, K x y * g y) := by rfl
            _ = ∑ x, (f x * g x - f x * (∑ y, K x y * g y)) := by rw [Finset.sum_sub_distrib]
            _ = ∑ x, f x * (g x - ∑ y, K x y * g y) := by
                  refine Finset.sum_congr rfl ?_; intro x _; ring

/-- Algebraic expansion of the square (`hSym` = self-adjointness of `A_K`). -/
lemma greenQ_sub_expand
    (K : ι → ι → ℝ)
    (hSym : ∀ f g : ι → ℝ, dotV (greenA K f) g = dotV f (greenA K g))
    (f u : ι → ℝ) :
    greenQ K (fun x => f x - u x)
      = greenQ K f - 2 * dotV (greenA K u) f + greenQ K u := by
  have hcross : dotV (greenA K f) u = dotV (greenA K u) f := by
    calc dotV (greenA K f) u = dotV f (greenA K u) := hSym f u
      _ = dotV (greenA K u) f := dotV_comm f (greenA K u)
  unfold greenQ
  rw [greenA_sub, dotV_sub_sub, hcross]; ring

/-- Complete-the-square identity: if `A_K u = h`, then
`2⟨h,f⟩ − Q_K(f) = ⟨h,u⟩ − Q_K(f−u)`. -/
lemma green_complete_square
    (K : ι → ι → ℝ)
    (hSym : ∀ f g : ι → ℝ, dotV (greenA K f) g = dotV f (greenA K g))
    (h u f : ι → ℝ) (hAu : ∀ x, greenA K u x = h x) :
    greenDual K h f = dotV h u - greenQ K (fun x => f x - u x) := by
  have hsub := greenQ_sub_expand K hSym f u
  have hAu_dot_f : dotV (greenA K u) f = dotV h f := by
    unfold dotV; refine Finset.sum_congr rfl ?_; intro x _; rw [hAu]
  have hQu : greenQ K u = dotV h u := by
    unfold greenQ dotV; refine Finset.sum_congr rfl ?_; intro x _; rw [hAu]
  unfold greenDual; rw [hAu_dot_f, hQu] at hsub; linarith

/-- The `≤` direction of Green-form duality: every test function is bounded by the Green value. -/
theorem green_form_bound
    (K : ι → ι → ℝ) (G : (ι → ℝ) → ι → ℝ)
    (hSym : ∀ f g : ι → ℝ, dotV (greenA K f) g = dotV f (greenA K g))
    (hG : ∀ h x, greenA K (G h) x = h x)
    (hQnonneg : ∀ f : ι → ℝ, 0 ≤ greenQ K f)
    (h f : ι → ℝ) :
    greenDual K h f ≤ dotV h (G h) := by
  have hsquare := green_complete_square K hSym h (G h) f (hG h)
  rw [hsquare]
  have hnonneg : 0 ≤ greenQ K (fun x => f x - G h x) := hQnonneg (fun x => f x - G h x)
  linarith

/-- The `≥` direction / attainment: plugging `f = Gh` gives equality. -/
theorem green_form_attain
    (K : ι → ι → ℝ) (G : (ι → ℝ) → ι → ℝ)
    (hG : ∀ h x, greenA K (G h) x = h x) (h : ι → ℝ) :
    greenDual K h (G h) = dotV h (G h) := by
  have hQ : greenQ K (G h) = dotV h (G h) := by
    unfold greenQ dotV; refine Finset.sum_congr rfl ?_; intro x _; rw [hG h x]
  unfold greenDual; rw [hQ]; ring

/-- Supremum-free formal duality: `⟨h, G h⟩` is the greatest value of `f ↦ 2⟨h,f⟩ − Q_K(f)`. -/
theorem green_form_duality_isGreatest
    (K : ι → ι → ℝ) (G : (ι → ℝ) → ι → ℝ)
    (hSym : ∀ f g : ι → ℝ, dotV (greenA K f) g = dotV f (greenA K g))
    (hG : ∀ h x, greenA K (G h) x = h x)
    (hQnonneg : ∀ f : ι → ℝ, 0 ≤ greenQ K f) (h : ι → ℝ) :
    IsGreatest (Set.range (fun f : ι → ℝ => greenDual K h f)) (dotV h (G h)) := by
  constructor
  · exact ⟨G h, green_form_attain K G hG h⟩
  · intro y hy
    rcases hy with ⟨f, rfl⟩
    exact green_form_bound K G hSym hG hQnonneg h f

/-- **Form domination ⟹ Green domination.**  If `Q_K(f) ≤ Λ·Q_R(f)` for all `f`, then
`⟨h, G_K h⟩ ≥ Λ⁻¹·⟨h, G_R h⟩`.  The constant is exactly `1/Λ`. -/
theorem green_domination_of_form_le
    (K R : ι → ι → ℝ) (GK GR : (ι → ℝ) → ι → ℝ) (Λ : ℝ)
    (hΛpos : 0 < Λ)
    (hSymK : ∀ f g : ι → ℝ, dotV (greenA K f) g = dotV f (greenA K g))
    (hGK : ∀ h x, greenA K (GK h) x = h x)
    (hGR : ∀ h x, greenA R (GR h) x = h x)
    (hQnonnegK : ∀ f : ι → ℝ, 0 ≤ greenQ K f)
    (hForm : ∀ f : ι → ℝ, greenQ K f ≤ Λ * greenQ R f) (h : ι → ℝ) :
    (1 / Λ) * dotV h (GR h) ≤ dotV h (GK h) := by
  set u : ι → ℝ := GR h with hu
  set f : ι → ℝ := fun x => (1 / Λ) * u x with hf
  have hupper : greenDual K h f ≤ dotV h (GK h) :=
    green_form_bound K GK hSymK hGK hQnonnegK h f
  have hdotf : dotV h f = (1 / Λ) * dotV h u := by rw [hf]; exact dotV_const_mul_right (1 / Λ) h u
  have hQRu : greenQ R u = dotV h u := by
    unfold greenQ dotV; refine Finset.sum_congr rfl ?_; intro x _; rw [hu, hGR h x]
  have hQRf : greenQ R f = (1 / Λ) ^ 2 * greenQ R u := by rw [hf]; exact greenQ_const_mul R (1 / Λ) u
  have hQK_le : greenQ K f ≤ (1 / Λ) * dotV h u := by
    calc greenQ K f ≤ Λ * greenQ R f := hForm f
      _ = Λ * ((1 / Λ) ^ 2 * greenQ R u) := by rw [hQRf]
      _ = (1 / Λ) * dotV h u := by rw [hQRu]; field_simp
  have hlower : (1 / Λ) * dotV h u ≤ greenDual K h f := by
    unfold greenDual; rw [hdotf]; linarith [hQK_le]
  exact le_trans hlower hupper

end AnalyticCombinatorics.Ch8.Partitions.Erdos
