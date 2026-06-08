import AnalyticCombinatorics.Ch8.Partitions.ITERGreen

/-!
# R7 Fact B via Doeblin: the finite-horizon Green potential is a subsolution for free

ChatGPT R7's key observation: the finite-`T` truncated Green potential

  `greenT T (x,y) = ∑_{t<T} (KresAct^[t] goodIndic) (x,y)`

(expected window occupation over `T` residual steps) is a Poisson **subsolution** of the residual
kernel `Kres` *automatically* — no recurrence needed.  The geometric/Poisson identity

  `KresAct (greenT T) = greenT T − goodIndic + KresAct^[T] goodIndic`

has a nonnegative tail, so `KresAct (greenT T) ≥ greenT T − goodIndic`, i.e. exactly the hypothesis the
banked `occupation_ge_green_tight` consumes.  This file banks that structural fact (pure finite-sum
algebra).  The entire remaining wall then collapses to the single expected-local-time lower bound
`greenT T (i,j) ≥ (1−ε)/δ` for high-rank comparable starts (the recurrence content), plus the ITER
instantiation to the killed Erdős kernel.  Opus-authored (vehicle ChatGPT R7).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

/-- Window indicator on pairs. -/
def goodIndic : α → α → ℝ := fun x y => if GoodW rnk W x y then (1 : ℝ) else 0

/-- One application of the residual kernel as an operator on pair-functions. -/
def KresAct (f : α → α → ℝ) : α → α → ℝ :=
  fun x y => ∑ a, ∑ b, Kres P rnk W x y a b * f a b

/-- Finite-horizon Green potential: expected window occupation over `T` residual steps. -/
def greenT (T : ℕ) : α → α → ℝ :=
  fun x y => ∑ t ∈ Finset.range T, (KresAct P rnk W)^[t] (goodIndic rnk W) x y

lemma goodIndic_nonneg (x y : α) : 0 ≤ goodIndic rnk W x y := by
  unfold goodIndic; split <;> norm_num

include hPnn hPmass in
lemma KresAct_nonneg {f : α → α → ℝ} (hf : ∀ x y, 0 ≤ f x y) (x y : α) :
    0 ≤ KresAct P rnk W f x y :=
  Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
    mul_nonneg (Kres_nonneg P rnk W hPnn hPmass x y a b) (hf a b)))

include hPnn hPmass in
lemma KresIter_nonneg (t : ℕ) :
    ∀ x y, 0 ≤ (KresAct P rnk W)^[t] (goodIndic rnk W) x y := by
  induction t with
  | zero => intro x y; simpa using goodIndic_nonneg rnk W x y
  | succ t ih =>
    intro x y
    rw [Function.iterate_succ', Function.comp_apply]
    exact KresAct_nonneg P rnk W hPnn hPmass ih x y

include hPnn hPmass in
/-- **Green Poisson identity (finite horizon).** -/
lemma greenT_poisson (T : ℕ) (x y : α) :
    KresAct P rnk W (greenT P rnk W T) x y
      = greenT P rnk W T x y - goodIndic rnk W x y
        + (KresAct P rnk W)^[T] (goodIndic rnk W) x y := by
  have hlin : KresAct P rnk W (greenT P rnk W T) x y
      = ∑ t ∈ Finset.range T, (KresAct P rnk W)^[t + 1] (goodIndic rnk W) x y := by
    simp only [KresAct, greenT]
    calc ∑ a, ∑ b, Kres P rnk W x y a b
            * ∑ t ∈ Finset.range T, (KresAct P rnk W)^[t] (goodIndic rnk W) a b
        = ∑ a, ∑ b, ∑ t ∈ Finset.range T,
            Kres P rnk W x y a b * (KresAct P rnk W)^[t] (goodIndic rnk W) a b := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
          rw [Finset.mul_sum]
      _ = ∑ a, ∑ t ∈ Finset.range T, ∑ b,
            Kres P rnk W x y a b * (KresAct P rnk W)^[t] (goodIndic rnk W) a b := by
          refine Finset.sum_congr rfl (fun a _ => ?_); rw [Finset.sum_comm]
      _ = ∑ t ∈ Finset.range T, ∑ a, ∑ b,
            Kres P rnk W x y a b * (KresAct P rnk W)^[t] (goodIndic rnk W) a b := by
          rw [Finset.sum_comm]
      _ = ∑ t ∈ Finset.range T, (KresAct P rnk W)^[t + 1] (goodIndic rnk W) x y := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          simp only [Function.iterate_succ', Function.comp_apply, KresAct]
  have hshift : ∑ t ∈ Finset.range T, (KresAct P rnk W)^[t + 1] (goodIndic rnk W) x y
      = (∑ t ∈ Finset.range T, (KresAct P rnk W)^[t] (goodIndic rnk W) x y)
        + (KresAct P rnk W)^[T] (goodIndic rnk W) x y
        - (KresAct P rnk W)^[0] (goodIndic rnk W) x y := by
    have e1 := Finset.sum_range_succ'
      (fun i => (KresAct P rnk W)^[i] (goodIndic rnk W) x y) T
    have e2 := Finset.sum_range_succ
      (fun i => (KresAct P rnk W)^[i] (goodIndic rnk W) x y) T
    simp only at e1 e2
    linarith [e1, e2]
  rw [hlin, hshift]
  simp only [Function.iterate_zero, id_eq]
  unfold greenT
  ring

include hPnn hPmass in
/-- **`greenT` is a Poisson subsolution of `Kres`** — exactly the hypothesis `occupation_ge_green_tight`
consumes.  No recurrence needed: it falls out of the nonnegative finite-horizon tail. -/
theorem greenT_subsolution (T : ℕ) (x y : α) :
    greenT P rnk W T x y - (if GoodW rnk W x y then (1 : ℝ) else 0)
      ≤ ∑ a, ∑ b, Kres P rnk W x y a b * greenT P rnk W T a b := by
  have hp := greenT_poisson P rnk W hPnn hPmass T x y
  have htail : 0 ≤ (KresAct P rnk W)^[T] (goodIndic rnk W) x y :=
    KresIter_nonneg P rnk W hPnn hPmass T x y
  have hKA : (∑ a, ∑ b, Kres P rnk W x y a b * greenT P rnk W T a b)
      = KresAct P rnk W (greenT P rnk W T) x y := rfl
  rw [hKA, hp]
  simp only [goodIndic] at *
  linarith [htail]

include hPnn hPmass in
/-- `greenT` is nonnegative. -/
theorem greenT_nonneg (T : ℕ) (x y : α) : 0 ≤ greenT P rnk W T x y :=
  Finset.sum_nonneg (fun t _ => KresIter_nonneg P rnk W hPnn hPmass t x y)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
