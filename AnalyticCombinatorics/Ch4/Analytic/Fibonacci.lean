import AnalyticCombinatorics.Ch4.Analytic.Rational
import AnalyticCombinatorics.Ch1.OGF.Fibonacci
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Fibonacci asymptotics from the dominant pole

This file factors the Fibonacci OGF denominator over `ℂ`, proves the
partial-fraction decomposition using the real golden-ratio constants cast to
`ℂ`, and applies the dominant-pole estimate from Chapter 4.
-/

open Filter Asymptotics
open scoped PowerSeries Topology BigOperators
open AnalyticCombinatorics.Ch1

noncomputable section

local notation "φc" => ((Real.goldenRatio : ℝ) : ℂ)
local notation "ψc" => ((Real.goldenConj : ℝ) : ℂ)
local notation "δ" => (φc - ψc)
local notation "A" => (φc / δ)
local notation "B" => (-ψc / δ)

private lemma hadd : φc + ψc = 1 := by
  exact_mod_cast Real.goldenRatio_add_goldenConj

private lemma hmul : φc * ψc = -1 := by
  exact_mod_cast Real.goldenRatio_mul_goldenConj

private lemma hδ : δ ≠ 0 := by
  have hδR : Real.goldenRatio - Real.goldenConj ≠ 0 := by
    rw [Real.goldenRatio_sub_goldenConj]
    positivity
  exact_mod_cast hδR

private lemma hAB : A + B = 1 := by
  rw [← add_div]
  have hnum : φc + -ψc = δ := by ring
  rw [hnum, div_self hδ]

private lemma hlin : A * ψc + B * φc = 0 := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

private lemma hφ : φc ≠ 0 := by
  exact_mod_cast Real.goldenRatio_ne_zero

private lemma hA : A ≠ 0 := by
  exact div_ne_zero hφ hδ

private lemma hgeom (a : ℂ) :
    PowerSeries.rescale a (PowerSeries.invUnitsSub (1 : ℂˣ)) *
      (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale a)
    (PowerSeries.invUnitsSub_mul_sub (u := (1 : ℂˣ)))
  simpa [PowerSeries.rescale_X] using h

private lemma hfact : (1 - (PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℂ) =
    (1 - PowerSeries.C φc * PowerSeries.X) *
      (1 - PowerSeries.C ψc * PowerSeries.X) := by
  have hCadd : (PowerSeries.C (φc + ψc) : PowerSeries ℂ) = 1 := by
    rw [hadd]
    simp
  have hCmul : (PowerSeries.C (φc * ψc) : PowerSeries ℂ) = -1 := by
    rw [hmul]
    simp
  calc
    (1 - (PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℂ)
        = 1 - PowerSeries.X - PowerSeries.X ^ 2 := by ring
    _ = 1 - PowerSeries.C (φc + ψc) * PowerSeries.X +
          PowerSeries.C (φc * ψc) * PowerSeries.X ^ 2 := by
        rw [hCadd, hCmul]
        ring
    _ = (1 - PowerSeries.C φc * PowerSeries.X) *
          (1 - PowerSeries.C ψc * PowerSeries.X) := by
        rw [map_add, map_mul]
        ring

theorem partialFraction_eq :
    PowerSeries.mapℂ CombClass.parts12.seq.ogf =
      PowerSeries.C A * PowerSeries.rescale φc (PowerSeries.invUnitsSub (1 : ℂˣ)) +
        PowerSeries.C B * PowerSeries.rescale ψc (PowerSeries.invUnitsSub (1 : ℂˣ)) := by
  let D : PowerSeries ℂ := 1 - (PowerSeries.X + PowerSeries.X ^ 2)
  let PF : PowerSeries ℂ :=
    PowerSeries.C A * PowerSeries.rescale φc (PowerSeries.invUnitsSub (1 : ℂˣ)) +
      PowerSeries.C B * PowerSeries.rescale ψc (PowerSeries.invUnitsSub (1 : ℂˣ))
  have hS : PowerSeries.mapℂ CombClass.parts12.seq.ogf * D = 1 := by
    have h := congrArg PowerSeries.mapℂ CombClass.ogf_seq_parts12
    simpa [D, PowerSeries.mapℂ] using h
  have hPF : PF * D = 1 := by
    let Gφ : PowerSeries ℂ :=
      PowerSeries.rescale φc (PowerSeries.invUnitsSub (1 : ℂˣ))
    let Gψ : PowerSeries ℂ :=
      PowerSeries.rescale ψc (PowerSeries.invUnitsSub (1 : ℂˣ))
    let Fφ : PowerSeries ℂ := 1 - PowerSeries.C φc * PowerSeries.X
    let Fψ : PowerSeries ℂ := 1 - PowerSeries.C ψc * PowerSeries.X
    have hφgeom : Gφ * Fφ = 1 := by
      simpa [Gφ, Fφ] using hgeom φc
    have hψgeom : Gψ * Fψ = 1 := by
      simpa [Gψ, Fψ] using hgeom ψc
    change PF * (1 - (PowerSeries.X + PowerSeries.X ^ 2)) = 1
    rw [hfact]
    change (PowerSeries.C A * Gφ + PowerSeries.C B * Gψ) * (Fφ * Fψ) = 1
    calc
      (PowerSeries.C A * Gφ + PowerSeries.C B * Gψ) * (Fφ * Fψ)
          = PowerSeries.C A * (Gφ * Fφ) * Fψ +
              PowerSeries.C B * (Gψ * Fψ) * Fφ := by ring
      _ = PowerSeries.C A * Fψ + PowerSeries.C B * Fφ := by
          rw [hφgeom, hψgeom]
          ring
      _ = PowerSeries.C (A + B) - PowerSeries.C (A * ψc + B * φc) *
            PowerSeries.X := by
          rw [map_add, map_add, map_mul, map_mul]
          ring
      _ = 1 := by
          rw [hAB, hlin]
          simp
  have hD0 : PowerSeries.constantCoeff D ≠ 0 := by
    simp [D]
  have hSinv : PowerSeries.mapℂ CombClass.parts12.seq.ogf = D⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one hD0).2 hS
  have hPFinv : PF = D⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one hD0).2 hPF
  exact hSinv.trans hPFinv.symm

theorem coeff_mapℂ_ogf_seq_parts12_isEquivalent :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n
        (PowerSeries.mapℂ CombClass.parts12.seq.ogf))
      ~[Filter.atTop] (fun n : ℕ => A * φc ^ n) := by
  have hψφ : ‖ψc‖ < ‖φc‖ := by
    have hψnonneg : 0 ≤ -Real.goldenConj := by
      linarith [Real.goldenConj_neg]
    calc
      ‖ψc‖ = ‖((-Real.goldenConj : ℝ) : ℂ)‖ := by
        rw [← norm_neg]
        simp
      _ = -Real.goldenConj := Complex.norm_of_nonneg hψnonneg
      _ < 1 := by
        linarith [Real.neg_one_lt_goldenConj]
      _ < Real.goldenRatio := Real.one_lt_goldenRatio
      _ = ‖φc‖ := by
        rw [Complex.norm_of_nonneg (le_of_lt Real.goldenRatio_pos)]
  have hPF := simplePoleSum_dominant_isEquivalent
    (s := (Finset.univ : Finset Bool)) (i0 := false)
    (c := fun b : Bool => if b then B else A)
    (a := fun b : Bool => if b then ψc else φc)
    (by simp) (by simpa using hφ) (by simpa using hA)
    (by
      intro i hi hne
      cases i
      · contradiction
      · simpa using hψφ)
  simpa [partialFraction_eq, add_comm, add_left_comm, add_assoc] using hPF

theorem coeff_mapℂ_ogf_seq_parts12 (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n
      (PowerSeries.mapℂ CombClass.parts12.seq.ogf) =
      (Nat.fib (n + 1) : ℂ) := by
  rw [PowerSeries.coeff_mapℂ, CombClass.coeff_ogf, counts_seq_parts12]
  norm_num

theorem fib_isEquivalent :
    (fun n : ℕ => (Nat.fib (n + 1) : ℂ))
      ~[Filter.atTop] (fun n : ℕ => A * φc ^ n) := by
  have hEq :
      (fun n : ℕ => (Nat.fib (n + 1) : ℂ)) =ᶠ[Filter.atTop]
        (fun n : ℕ =>
          PowerSeries.coeff (R := ℂ) n
            (PowerSeries.mapℂ CombClass.parts12.seq.ogf)) :=
    Eventually.of_forall fun n => (coeff_mapℂ_ogf_seq_parts12 n).symm
  exact hEq.trans_isEquivalent coeff_mapℂ_ogf_seq_parts12_isEquivalent
