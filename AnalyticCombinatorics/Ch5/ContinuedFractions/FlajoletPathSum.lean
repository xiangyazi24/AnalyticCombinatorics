import Mathlib
import AnalyticCombinatorics.Ch5.ContinuedFractions.Flajolet

/-!
# Path-sum coefficients for Flajolet's bounded continued fraction

This file bridges the literal finite path sum from `MotzkinPath` to the
first-return recursive coefficients used by `W`.
-/

open scoped BigOperators PowerSeries

namespace AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum

noncomputable section

/- Splitting `Fintype.univ` over the recursive `Sum`/`Sigma` path code creates
large finite-sum goals after unfolding `pathWeight`. -/
set_option maxHeartbeats 800000

open AnalyticCombinatorics.Ch5.ContinuedFractions

/-- Summing over a recursive type is unchanged by the `Eq.mp` to its unfolded code. -/
private theorem fintype_sum_eq_mp {α β : Type u} {M : Type v}
    [Fintype α] [Fintype β] [AddCommMonoid M]
    (h : α = β) (f : β → M) :
    (∑ x : α, f (h.mp x)) = ∑ x : β, f x := by
  simpa [Equiv.cast, cast] using Equiv.sum_comp (Equiv.cast h) f

/-- The literal path sum satisfies the same first-return recursion as `Wcoeff`. -/
theorem WpathSum_eq_Wcoeff {R : Type*} [CommRing R] (h n : ℕ) (a b c : ℕ → R) :
    WpathSum h a b c n = Wcoeff h a b c n := by
  induction h, a, b, c, n using Wcoeff.induct with
  | case1 h a b c =>
      simp [WpathSum, pathWeight, MotzkinPath]
  | case2 a b c n ih =>
      rw [WpathSum, Wcoeff]
      simp only [pathWeight]
      change
        (∑ x : MotzkinPath 0 (n + 1),
          c 0 * pathWeight a b c 0 n ((MotzkinPath.eq_2 n).mp x)) =
          c 0 * Wcoeff 0 a b c n
      rw [fintype_sum_eq_mp (MotzkinPath.eq_2 n)
        (fun x : MotzkinPath 0 n => c 0 * pathWeight a b c 0 n x)]
      rw [← Finset.mul_sum]
      exact congrArg (fun x => c 0 * x) ih
  | case3 h a b c =>
      simp [WpathSum, Wcoeff, pathWeight, MotzkinPath]
  | case4 h a b c n ihLevel ihInner ihRest =>
      rw [WpathSum, Wcoeff]
      simp only [pathWeight]
      change
        (∑ x : MotzkinPath h.succ n.succ.succ,
          (fun y :
              MotzkinPath (h + 1) (n + 1) ⊕
                (Σ i : Fin (n + 1),
                  MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)) =>
            match y with
            | Sum.inl rest => c 0 * pathWeight a b c (h + 1) (n + 1) rest
            | Sum.inr arch =>
                a 0 * b 0 *
                  pathWeight (shift a) (shift b) (shift c) h arch.1.1 arch.2.1 *
                    pathWeight a b c (h + 1) (n - arch.1.1) arch.2.2)
            ((MotzkinPath.eq_4 h n).mp x)) =
          c 0 * Wcoeff (h + 1) a b c (n + 1) +
            a 0 * b 0 *
              ∑ i : Fin (n + 1),
                Wcoeff h (shift a) (shift b) (shift c) i.1 *
                  Wcoeff (h + 1) a b c (n - i.1)
      calc
        (∑ x : MotzkinPath h.succ n.succ.succ,
          (fun y :
              MotzkinPath (h + 1) (n + 1) ⊕
                (Σ i : Fin (n + 1),
                  MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)) =>
            match y with
            | Sum.inl rest => c 0 * pathWeight a b c (h + 1) (n + 1) rest
            | Sum.inr arch =>
                a 0 * b 0 *
                  pathWeight (shift a) (shift b) (shift c) h arch.1.1 arch.2.1 *
                    pathWeight a b c (h + 1) (n - arch.1.1) arch.2.2)
            ((MotzkinPath.eq_4 h n).mp x))
            =
            ∑ x :
              MotzkinPath (h + 1) (n + 1) ⊕
                (Σ i : Fin (n + 1),
                  MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)),
              match x with
              | Sum.inl rest => c 0 * pathWeight a b c (h + 1) (n + 1) rest
              | Sum.inr arch =>
                  a 0 * b 0 *
                    pathWeight (shift a) (shift b) (shift c) h arch.1.1 arch.2.1 *
                      pathWeight a b c (h + 1) (n - arch.1.1) arch.2.2 := by
          exact fintype_sum_eq_mp (MotzkinPath.eq_4 h n)
            (fun x :
                MotzkinPath (h + 1) (n + 1) ⊕
                  (Σ i : Fin (n + 1),
                    MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)) =>
              match x with
              | Sum.inl rest => c 0 * pathWeight a b c (h + 1) (n + 1) rest
              | Sum.inr arch =>
                a 0 * b 0 *
                  pathWeight (shift a) (shift b) (shift c) h arch.1.1 arch.2.1 *
                    pathWeight a b c (h + 1) (n - arch.1.1) arch.2.2)
        _ =
            (∑ rest : MotzkinPath (h + 1) (n + 1),
              c 0 * pathWeight a b c (h + 1) (n + 1) rest) +
              ∑ arch :
                  (Σ i : Fin (n + 1),
                    MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)),
                a 0 * b 0 *
                  pathWeight (shift a) (shift b) (shift c) h arch.1.1 arch.2.1 *
                    pathWeight a b c (h + 1) (n - arch.1.1) arch.2.2 := by
          rw [Fintype.sum_sum_type]
        _ =
            c 0 * WpathSum (h + 1) a b c (n + 1) +
              a 0 * b 0 *
                ∑ i : Fin (n + 1),
                  WpathSum h (shift a) (shift b) (shift c) i.1 *
                  WpathSum (h + 1) a b c (n - i.1) := by
          congr 1
          · rw [← Finset.mul_sum]
            rfl
          · rw [Fintype.sum_sigma]
            simp_rw [Fintype.sum_prod_type]
            simp_rw [mul_assoc]
            simp_rw [← Finset.mul_sum]
            apply congrArg (fun x => a 0 * (b 0 * x))
            apply Finset.sum_congr rfl
            intro i _hi
            rw [← Finset.sum_mul]
            rfl
        _ =
            c 0 * Wcoeff (h + 1) a b c (n + 1) +
              a 0 * b 0 *
                ∑ i : Fin (n + 1),
                  Wcoeff h (shift a) (shift b) (shift c) i.1 *
                    Wcoeff (h + 1) a b c (n - i.1) := by
          rw [ihLevel]
          apply congrArg (fun x =>
            c 0 * Wcoeff (h + 1) a b c (n + 1) + a 0 * b 0 * x)
          apply Finset.sum_congr rfl
          intro i _hi
          rw [ihInner i, ihRest i]

/-- Coefficients of the bounded J-fraction are the literal finite path sums. -/
theorem coeff_JFraction_eq_pathSum {R : Type*} [CommRing R]
    (h n : ℕ) (a b c : ℕ → R) :
    PowerSeries.coeff (R := R) n (JFraction h a b c) = WpathSum h a b c n := by
  rw [← flajolet_cf h a b c, coeff_W, WpathSum_eq_Wcoeff]

end

end AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum
