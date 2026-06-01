import AnalyticCombinatorics.Ch4.Analytic.Rational
import AnalyticCombinatorics.Ch4.Analytic.SingularityInteger

open Filter Asymptotics
open scoped PowerSeries Topology BigOperators

noncomputable section

namespace PowerSeries

lemma coeff_C_mul_rescale_invOneSubPow (c a₀ : ℂ) (d n : ℕ) :
    coeff (R := ℂ) n (C c * rescale a₀ (invOneSubPow ℂ (d + 1)).val) =
      c * a₀ ^ n * (Nat.choose (d + n) d : ℂ) := by
  rw [coeff_C_mul, coeff_rescale_invOneSubPow]
  ring

end PowerSeries

lemma shifted_choose_complex_isEquivalent (d : ℕ) :
    (fun n : ℕ => (Nat.choose (d + n) d : ℂ)) ~[atTop]
      (fun n : ℕ => (n : ℂ)^d / (d.factorial : ℂ)) := by
  simpa [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, Nat.add_comm]
    using coeff_invOneSubPow_isEquivalent d

lemma repeatedPole_coeff_model_isEquivalent (c a₀ : ℂ) (d : ℕ) :
    (fun n : ℕ => c * a₀ ^ n * (Nat.choose (d + n) d : ℂ)) ~[atTop]
      (fun n : ℕ => c * a₀ ^ n * ((n : ℂ)^d / (d.factorial : ℂ))) := by
  have hchoose := shifted_choose_complex_isEquivalent d
  have hsame : (fun n : ℕ => c * a₀ ^ n) ~[atTop] (fun n : ℕ => c * a₀ ^ n) :=
    IsEquivalent.refl (l := atTop) (u := fun n : ℕ => c * a₀ ^ n)
  exact hsame.mul hchoose

theorem coeff_repeatedPole_isEquivalent (c a₀ : ℂ) (_ha₀ : a₀ ≠ 0) (_hc : c ≠ 0)
    (d : ℕ) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
      (PowerSeries.C c * PowerSeries.rescale a₀
        (PowerSeries.invOneSubPow ℂ (d + 1)).val))
      ~[atTop]
    (fun n : ℕ => c * a₀^n * ((n : ℂ)^d / (d.factorial : ℂ))) := by
  have hcoeff :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
        (PowerSeries.C c * PowerSeries.rescale a₀
          (PowerSeries.invOneSubPow ℂ (d + 1)).val)) =
        (fun n : ℕ => c * a₀ ^ n * (Nat.choose (d + n) d : ℂ)) := by
    funext n
    exact PowerSeries.coeff_C_mul_rescale_invOneSubPow c a₀ d n
  rw [hcoeff]
  exact repeatedPole_coeff_model_isEquivalent c a₀ d
