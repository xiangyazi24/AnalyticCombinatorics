import AnalyticCombinatorics.Ch3.BGF.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Ch3 -- Binary words marked by number of ones

The class of binary words of length `n`, with the bivariate parameter counting
the number of ones, has BGF `1 / (1 - (1 + u) z)`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Binary words, with the parameter counting the number of `true` entries. -/
noncomputable def ParamClass.binaryWords : ParamClass where
  Obj n := Fin n → Bool
  finObj _ := inferInstance
  param _ f := (Finset.univ.filter (fun i => f i = true)).card

private noncomputable def binaryWordsEquivFinset (n : ℕ) :
    (Fin n → Bool) ≃ Finset (Fin n) where
  toFun f := Finset.univ.filter fun i => f i = true
  invFun s := fun i => decide (i ∈ s)
  left_inv f := by
    funext i
    cases h : f i <;> simp [h]
  right_inv s := by
    ext i
    simp

/-- Binary words of length `n` with exactly `k` ones are counted by `choose n k`. -/
lemma bcounts_binaryWords (n k : ℕ) :
    ParamClass.binaryWords.bcounts n k = n.choose k := by
  classical
  rw [ParamClass.bcounts, ParamClass.binaryWords]
  change Fintype.card
      {f : Fin n → Bool // (Finset.univ.filter (fun i => f i = true)).card = k} =
    n.choose k
  let e :
      {f : Fin n → Bool // (Finset.univ.filter (fun i => f i = true)).card = k} ≃
        {s : Finset (Fin n) // s.card = k} :=
    { toFun := fun f => ⟨Finset.univ.filter (fun i => f.1 i = true), f.2⟩
      invFun := fun s => ⟨fun i => decide (i ∈ s.1), by
        have hset :
            (Finset.univ.filter (fun i => decide (i ∈ s.1) = true)) = s.1 := by
          ext i
          simp
        rw [hset, s.2]⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        cases h : f.1 i <;> simp [h]
      right_inv := by
        intro s
        apply Subtype.ext
        ext i
        simp }
  calc
    Fintype.card
        {f : Fin n → Bool // (Finset.univ.filter (fun i => f i = true)).card = k}
        = Fintype.card {s : Finset (Fin n) // s.card = k} :=
          Fintype.card_congr e
    _ = n.choose k := by
          rw [Fintype.card_finset_len, Fintype.card_fin]

private lemma sum_pow_card_finset (α : Type*) [Fintype α] [DecidableEq α] :
    (∑ s : Finset α, (Polynomial.X : ℚ[X]) ^ s.card) =
      (1 + Polynomial.X : ℚ[X]) ^ Fintype.card α := by
  simpa [Finset.prod_eq_pow_card] using
    (Finset.prod_one_add (s := (Finset.univ : Finset α))
      (f := fun _ : α => (Polynomial.X : ℚ[X]))).symm

/-- The size-`n` parameter polynomial for binary words is `(1 + u)^n`. -/
lemma paramPoly_binaryWords (n : ℕ) :
    ParamClass.binaryWords.paramPoly n = (1 + Polynomial.X : ℚ[X]) ^ n := by
  classical
  rw [ParamClass.paramPoly, ParamClass.binaryWords]
  change (∑ f : Fin n → Bool,
      (Polynomial.X : ℚ[X]) ^
        (Finset.univ.filter (fun i => f i = true)).card) =
    (1 + Polynomial.X : ℚ[X]) ^ n
  let e : (Fin n → Bool) ≃ Finset (Fin n) := binaryWordsEquivFinset n
  calc
    (∑ f : Fin n → Bool,
        (Polynomial.X : ℚ[X]) ^
          (Finset.univ.filter (fun i => f i = true)).card)
        = ∑ s : Finset (Fin n),
            (Polynomial.X : ℚ[X]) ^
              (Finset.univ.filter (fun i => e.symm s i = true)).card := by
          simpa using
            (Equiv.sum_comp e.symm
              (fun f : Fin n → Bool =>
                (Polynomial.X : ℚ[X]) ^
                  (Finset.univ.filter (fun i => f i = true)).card)).symm
    _ = ∑ s : Finset (Fin n), (Polynomial.X : ℚ[X]) ^ s.card := by
          refine Finset.sum_congr rfl fun s _ => ?_
          have hset :
              (Finset.univ.filter (fun i => e.symm s i = true)) = s := by
            ext i
            simp [e, binaryWordsEquivFinset]
          rw [hset]
    _ = (1 + Polynomial.X : ℚ[X]) ^ n := by
          rw [sum_pow_card_finset, Fintype.card_fin]

private lemma coeff_mul_C_mul_X (F : ℚ[X]⟦X⟧) (A : ℚ[X]) (n : ℕ) :
    PowerSeries.coeff (n + 1) (F * (PowerSeries.C A * PowerSeries.X)) =
      PowerSeries.coeff n F * A := by
  rw [show F * (PowerSeries.C A * PowerSeries.X) =
      (F * PowerSeries.C A) * PowerSeries.X by ring]
  rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]

/-- The BGF of binary words marked by number of ones is
`1 / (1 - (1 + u)z)`, stated as a formal power series identity. -/
theorem ParamClass.bgf_binaryWords_closed :
    ParamClass.binaryWords.bgf *
        (1 - PowerSeries.C (1 + Polynomial.X : ℚ[X]) *
          (PowerSeries.X : ℚ[X]⟦X⟧)) =
      1 := by
  classical
  let F : ℚ[X]⟦X⟧ := ParamClass.binaryWords.bgf
  let A : ℚ[X] := 1 + Polynomial.X
  have hF : ∀ n : ℕ, PowerSeries.coeff n F = A ^ n := by
    intro n
    simp [F, A, ParamClass.bgf, paramPoly_binaryWords]
  have hmain : F * (1 - PowerSeries.C A * (PowerSeries.X : ℚ[X]⟦X⟧)) = 1 := by
    have expand : F * (1 - PowerSeries.C A * (PowerSeries.X : ℚ[X]⟦X⟧)) =
        F - F * (PowerSeries.C A * (PowerSeries.X : ℚ[X]⟦X⟧)) := by
      ring
    rw [expand]
    apply PowerSeries.ext
    intro n
    rcases n with _ | n
    · rw [map_sub, hF 0]
      simp
    · rw [map_sub, hF (n + 1), coeff_mul_C_mul_X F A n, hF n]
      simp
      rw [pow_succ']
      ring
  simpa [F, A] using hmain

/-- Evaluating the marker at `u = 1` recovers the ordinary generating function. -/
lemma evalU1_binaryWords :
    evalU 1 ParamClass.binaryWords.bgf =
      ParamClass.binaryWords.toCombClass.ogf := by
  simpa using ParamClass.evalU1_bgf ParamClass.binaryWords

end AnalyticCombinatorics.Ch1
