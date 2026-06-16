import AnalyticCombinatorics.Ch4.Analytic.LogSqCoeff
import AnalyticCombinatorics.Ch4.Analytic.LogFaithful
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Finset.Powerset

/-!
# General logarithmic coefficient hierarchy: GF coefficient identity

This file is the coefficient-identity layer for

  `(1 - z)^(-α) · (-log (1 - z))^k`.

It contains only:

* the elementary-symmetric closed coefficient scale,
* the recursive formal GF `logKGF`,
* formal ODE recurrences,
* the closed-form recurrence,
* and the GF ↔ closed coefficient identity.

No asymptotics and no analytic faithfulness are included here.
-/

open scoped BigOperators PowerSeries

noncomputable section

namespace AnalyticCombinatorics

open PowerSeries

/-- Elementary symmetric function in the shifted reciprocals
`{(α+j)⁻¹ | j < n}`. -/
def shiftedElemSymmℂ (α : ℂ) (k n : ℕ) : ℂ :=
  ∑ s ∈ (Finset.range n).powersetCard k,
    ∏ j ∈ s, (α + (j : ℂ))⁻¹

/-- Closed coefficient scale for
`(1-z)^(-α) · (-log(1-z))^k`.

The factor `k!` is essential:
`2! e₂ = H² - H₂`, recovering the banked log² coefficient. -/
def logKCoeffℂ (α : ℂ) (k n : ℕ) : ℂ :=
  (k.factorial : ℂ) * binCoeffℂ α n * shiftedElemSymmℂ α k n

/-- Recursive formal GF for the `k`-th logarithmic singularity. -/
noncomputable def logKGF (α : ℂ) : ℕ → PowerSeries ℂ
  | 0 => oneSubCpowGF α
  | k + 1 => logKGF α k * logGF

/-- The `k = 1` recursive GF is the banked one-log GF. -/
theorem logKGF_one (α : ℂ) :
    logKGF α 1 = logSingularityGF α := by
  simp [logKGF, logSingularityGF]

/-- The `k = 2` recursive GF is the banked squared-log GF. -/
theorem logKGF_two (α : ℂ) :
    logKGF α 2 = logSqGF α := by
  simp [logKGF, logSqGF, logSingularityGF, mul_assoc]

/-! ## Coefficients of `(1 - X)·F'` -/

/-- Coefficient of `(1-X)·F'`, expressed in the recurrence-friendly form. -/
private theorem coeff_one_sub_X_mul_derivativeFun (F : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n
      ((1 - PowerSeries.X) * PowerSeries.derivativeFun F)
      =
    ((n : ℂ) + 1) * PowerSeries.coeff (R := ℂ) (n + 1) F
      - (n : ℂ) * PowerSeries.coeff (R := ℂ) n F := by
  have hsplit :
      (1 - PowerSeries.X) * PowerSeries.derivativeFun F =
        PowerSeries.derivativeFun F - PowerSeries.X * PowerSeries.derivativeFun F := by
    ring
  cases n with
  | zero =>
      rw [hsplit, map_sub]
      simp [PowerSeries.coeff_derivativeFun]
  | succ n =>
      rw [hsplit, map_sub, coeff_succ_X_mul,
        PowerSeries.coeff_derivativeFun, PowerSeries.coeff_derivativeFun]
      push_cast
      ring

/-! ## Formal ODEs -/

/-- Algebraic base ODE:
`(1-X)·d/dX (1-X)^(-α) = α(1-X)^(-α)`. -/
theorem oneSubCpowGF_ode (α : ℂ) :
    (1 - PowerSeries.X) * PowerSeries.derivativeFun (oneSubCpowGF α)
      =
    PowerSeries.C α * oneSubCpowGF α := by
  ext n
  rw [coeff_one_sub_X_mul_derivativeFun, PowerSeries.coeff_C_mul]
  simp [oneSubCpowGF, PowerSeries.coeff_mk]
  have hrec := binCoeffℂ_succ α n
  linear_combination hrec

/-- Logarithm ODE: `(1-X)·d/dX logGF = 1`. -/
theorem logGF_ode :
    (1 - PowerSeries.X) * PowerSeries.derivativeFun logGF
      =
    (1 : PowerSeries ℂ) := by
  ext n
  rw [coeff_one_sub_X_mul_derivativeFun]
  cases n with
  | zero =>
      simp [logGF, logCoeffℂ, PowerSeries.coeff_mk]
  | succ n =>
      have h1 : (1 : ℂ) + (n : ℂ) ≠ 0 := by
        rw [show (1 : ℂ) + (n : ℂ) = ((n + 1 : ℕ) : ℂ) by push_cast; ring]
        exact_mod_cast (by omega : (n + 1 : ℕ) ≠ 0)
      have h2 : (2 : ℂ) + (n : ℂ) ≠ 0 := by
        rw [show (2 : ℂ) + (n : ℂ) = ((n + 2 : ℕ) : ℂ) by push_cast; ring]
        exact_mod_cast (by omega : (n + 2 : ℕ) ≠ 0)
      simp [logGF, logCoeffℂ, PowerSeries.coeff_mk]
      linear_combination inv_mul_cancel₀ h2 - inv_mul_cancel₀ h1

/-- Formal ODE for the recursive `logKGF` hierarchy:
`(1-X)·F'_{k+1} = αF_{k+1} + (k+1)F_k`. -/
theorem logKGF_ode_succ (α : ℂ) (k : ℕ) :
    (1 - PowerSeries.X) * PowerSeries.derivativeFun (logKGF α (k + 1))
      =
    PowerSeries.C α * logKGF α (k + 1)
      + PowerSeries.C (((k + 1 : ℕ) : ℂ)) * logKGF α k := by
  induction k with
  | zero =>
      have hpow := oneSubCpowGF_ode α
      have hlog := logGF_ode
      calc
        (1 - PowerSeries.X) *
            PowerSeries.derivativeFun (logKGF α (0 + 1))
            =
          (1 - PowerSeries.X) *
            PowerSeries.derivativeFun (oneSubCpowGF α * logGF) := by
              simp [logKGF]
        _ =
          ((1 - PowerSeries.X) * PowerSeries.derivativeFun (oneSubCpowGF α)) * logGF
            + oneSubCpowGF α *
              ((1 - PowerSeries.X) * PowerSeries.derivativeFun logGF) := by
              rw [PowerSeries.derivativeFun_mul]
              simp only [smul_eq_mul]
              ring
        _ =
          (PowerSeries.C α * oneSubCpowGF α) * logGF
            + oneSubCpowGF α * (1 : PowerSeries ℂ) := by
              rw [hpow, hlog]
        _ =
          PowerSeries.C α * logKGF α (0 + 1)
            + PowerSeries.C (((0 + 1 : ℕ) : ℂ)) * logKGF α 0 := by
              simp [logKGF]
              ring
  | succ k ih =>
      have hlog := logGF_ode
      have hCsucc :
          PowerSeries.C (((k + 2 : ℕ) : ℂ)) =
            PowerSeries.C (((k + 1 : ℕ) : ℂ)) + 1 := by
        rw [show (((k + 2 : ℕ) : ℂ)) = (((k + 1 : ℕ) : ℂ)) + 1 by push_cast; ring,
          map_add, map_one]
      calc
        (1 - PowerSeries.X) *
            PowerSeries.derivativeFun (logKGF α (Nat.succ k + 1))
            =
          (1 - PowerSeries.X) *
            PowerSeries.derivativeFun (logKGF α (k + 1) * logGF) := by
              simp [logKGF]
        _ =
          ((1 - PowerSeries.X) * PowerSeries.derivativeFun (logKGF α (k + 1))) * logGF
            + logKGF α (k + 1) *
              ((1 - PowerSeries.X) * PowerSeries.derivativeFun logGF) := by
              rw [PowerSeries.derivativeFun_mul]
              simp only [smul_eq_mul]
              ring
        _ =
          (PowerSeries.C α * logKGF α (k + 1)
              + PowerSeries.C (((k + 1 : ℕ) : ℂ)) * logKGF α k) * logGF
            + logKGF α (k + 1) * (1 : PowerSeries ℂ) := by
              rw [ih, hlog]
        _ =
          PowerSeries.C α * logKGF α (Nat.succ k + 1)
            + PowerSeries.C (((Nat.succ k + 1 : ℕ) : ℂ)) * logKGF α (Nat.succ k) := by
              simp [logKGF, hCsucc]
              ring

/-- Coefficient recurrence extracted from the formal ODE:
`(n+1)T_{k+1}(n+1) = (α+n)T_{k+1}(n) + (k+1)T_k(n)`. -/
theorem coeff_logKGF_succ_recurrence (α : ℂ) (k n : ℕ) :
    ((n : ℂ) + 1) *
        PowerSeries.coeff (R := ℂ) (n + 1) (logKGF α (k + 1))
      =
    (α + n) *
        PowerSeries.coeff (R := ℂ) n (logKGF α (k + 1))
      + (((k + 1 : ℕ) : ℂ)) *
        PowerSeries.coeff (R := ℂ) n (logKGF α k) := by
  have h :=
    congrArg (fun F : PowerSeries ℂ => PowerSeries.coeff (R := ℂ) n F)
      (logKGF_ode_succ α k)
  simp only [coeff_one_sub_X_mul_derivativeFun, map_add, PowerSeries.coeff_C_mul] at h
  linear_combination h

/-! ## Elementary-symmetric insertion recurrence -/

@[simp] theorem shiftedElemSymmℂ_zero (α : ℂ) (n : ℕ) :
    shiftedElemSymmℂ α 0 n = 1 := by
  simp [shiftedElemSymmℂ]

@[simp] theorem shiftedElemSymmℂ_succ_zero (α : ℂ) (k : ℕ) :
    shiftedElemSymmℂ α (k + 1) 0 = 0 := by
  rw [shiftedElemSymmℂ, Finset.range_zero,
    Finset.powersetCard_eq_empty.mpr (by simp), Finset.sum_empty]

private theorem powersetCard_insert_succ_eq_union
    {α : Type*} [DecidableEq α] (a : α) (s : Finset α) (ha : a ∉ s) (k : ℕ) :
    (insert a s).powersetCard (k + 1)
      =
    s.powersetCard (k + 1) ∪
      (s.powersetCard k).image (fun t : Finset α => insert a t) := by
  ext t
  constructor
  · intro ht
    rw [Finset.mem_union, Finset.mem_image]
    rw [Finset.mem_powersetCard] at ht
    rcases ht with ⟨htsub, htcard⟩
    by_cases hat : a ∈ t
    · right
      refine ⟨t.erase a, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        constructor
        · intro x hx
          have hxt : x ∈ t := (Finset.mem_erase.mp hx).2
          have hxne : x ≠ a := (Finset.mem_erase.mp hx).1
          have hxins := htsub hxt
          rw [Finset.mem_insert] at hxins
          rcases hxins with hxa | hxs
          · exact False.elim (hxne hxa)
          · exact hxs
        · rw [Finset.card_erase_of_mem hat]
          omega
      · exact Finset.insert_erase hat
    · left
      rw [Finset.mem_powersetCard]
      constructor
      · intro x hx
        have hxins := htsub hx
        rw [Finset.mem_insert] at hxins
        rcases hxins with hxa | hxs
        · subst hxa
          exact False.elim (hat hx)
        · exact hxs
      · exact htcard
  · intro ht
    rw [Finset.mem_union, Finset.mem_image] at ht
    rw [Finset.mem_powersetCard]
    rcases ht with ht | ht
    · rw [Finset.mem_powersetCard] at ht
      rcases ht with ⟨htsub, htcard⟩
      constructor
      · intro x hx
        exact Finset.mem_insert_of_mem (htsub hx)
      · exact htcard
    · rcases ht with ⟨u, hu, rfl⟩
      rw [Finset.mem_powersetCard] at hu
      rcases hu with ⟨husub, hucard⟩
      have hau : a ∉ u := fun hau => ha (husub hau)
      constructor
      · intro x hx
        rw [Finset.mem_insert] at hx ⊢
        rcases hx with hxa | hxu
        · exact Or.inl hxa
        · exact Or.inr (husub hxu)
      · rw [Finset.card_insert_of_notMem hau, hucard]

/-- Inserting the new reciprocal `(α+n)⁻¹` into the elementary symmetric functions. -/
theorem shiftedElemSymmℂ_succ_n (α : ℂ) (k n : ℕ) :
    shiftedElemSymmℂ α (k + 1) (n + 1)
      =
    shiftedElemSymmℂ α (k + 1) n
      + (α + (n : ℂ))⁻¹ * shiftedElemSymmℂ α k n := by
  classical
  have hnS : n ∉ Finset.range n := by
    simp
  have hrange : Finset.range (n + 1) = insert n (Finset.range n) := by
    ext j
    simp
    omega
  have hsplit :
      (insert n (Finset.range n)).powersetCard (k + 1)
        =
      (Finset.range n).powersetCard (k + 1) ∪
        ((Finset.range n).powersetCard k).image (fun t : Finset ℕ => insert n t) :=
    powersetCard_insert_succ_eq_union n (Finset.range n) hnS k
  simp only [shiftedElemSymmℂ]
  rw [hrange, hsplit]
  have hdisj :
      Disjoint ((Finset.range n).powersetCard (k + 1))
        (((Finset.range n).powersetCard k).image (fun t : Finset ℕ => insert n t)) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    rw [Finset.mem_image] at ht2
    rcases ht2 with ⟨u, hu, rfl⟩
    rw [Finset.mem_powersetCard] at ht1
    exact hnS (ht1.1 (by simp))
  rw [Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image (by
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hu hv
    have hnu : n ∉ u := fun h => hnS (hu.1 h)
    have hnv : n ∉ v := fun h => hnS (hv.1 h)
    have herase := congrArg (fun t : Finset ℕ => t.erase n) huv
    simpa [Finset.erase_insert hnu, Finset.erase_insert hnv] using herase)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro u hu
  rw [Finset.mem_powersetCard] at hu
  have hnu : n ∉ u := fun h => hnS (hu.1 h)
  rw [Finset.prod_insert hnu]

/-! ## Closed-form coefficient recurrence -/

/-- Base `k = 0`: the closed log⁰ coefficient is the binomial coefficient and satisfies
the usual binomial recurrence. -/
theorem logKCoeffℂ_zero_recurrence (α : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * logKCoeffℂ α 0 (n + 1)
      =
    (α + n) * logKCoeffℂ α 0 n := by
  simpa [logKCoeffℂ, shiftedElemSymmℂ_zero]
    using binCoeffℂ_succ α n

/-- Closed coefficient recurrence:
`(n+1)T_{k+1}(n+1) = (α+n)T_{k+1}(n) + (k+1)T_k(n)`. -/
theorem logKCoeffℂ_succ_recurrence
    (α : ℂ) (hα : ∀ m : ℕ, α ≠ -(m : ℂ))
    (k n : ℕ) :
    ((n : ℂ) + 1) * logKCoeffℂ α (k + 1) (n + 1)
      =
    (α + n) * logKCoeffℂ α (k + 1) n
      + (((k + 1 : ℕ) : ℂ)) * logKCoeffℂ α k n := by
  have hαn : α + (n : ℂ) ≠ 0 := by
    intro h
    exact hα n (eq_neg_of_add_eq_zero_left h)
  have hcancel : (α + (n : ℂ)) * (α + (n : ℂ))⁻¹ = 1 :=
    mul_inv_cancel₀ hαn
  have hrec := binCoeffℂ_succ α n
  let c : ℂ := ((k + 1 : ℕ) : ℂ)
  let F : ℂ := ((k.factorial : ℕ) : ℂ)
  let A : ℂ := binCoeffℂ α n
  let B : ℂ := binCoeffℂ α (n + 1)
  let E : ℂ := shiftedElemSymmℂ α (k + 1) n
  let e : ℂ := shiftedElemSymmℂ α k n
  let d : ℂ := α + (n : ℂ)
  let s : ℂ := (n : ℂ) + 1
  have hrec' : s * B = d * A := by
    dsimp [s, B, d, A]
    exact hrec
  have hcancel' : d * d⁻¹ = 1 := by
    dsimp [d]
    exact hcancel
  have hfac : (((k + 1).factorial : ℕ) : ℂ) = c * F := by
    dsimp [c, F]
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [logKCoeffℂ, logKCoeffℂ, logKCoeffℂ, shiftedElemSymmℂ_succ_n, hfac]
  change
    s * ((c * F) * B * (E + d⁻¹ * e))
      =
    d * ((c * F) * A * E) + c * (F * A * e)
  calc
    s * ((c * F) * B * (E + d⁻¹ * e))
        = (c * F) * (s * B) * (E + d⁻¹ * e) := by
          ring
    _ = (c * F) * (d * A) * (E + d⁻¹ * e) := by
          rw [hrec']
    _ = d * ((c * F) * A * E) + (c * F) * A * (d * d⁻¹) * e := by
          ring
    _ = d * ((c * F) * A * E) + c * (F * A * e) := by
          rw [hcancel']
          ring

/-! ## GF coefficient identity -/

/-- The recursive formal GF coefficients equal the closed elementary-symmetric scale. -/
theorem coeff_logKGF_eq_logKCoeffℂ
    (α : ℂ) (hα : ∀ m : ℕ, α ≠ -(m : ℂ))
    (k n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (logKGF α k)
      = logKCoeffℂ α k n := by
  induction k generalizing n with
  | zero =>
      simp [logKGF, logKCoeffℂ, shiftedElemSymmℂ_zero, oneSubCpowGF]
  | succ k ihk =>
      induction n with
      | zero =>
          have hlog0 : PowerSeries.coeff (R := ℂ) 0 logGF = 0 := by
            simp [logGF, logCoeffℂ]
          calc
            PowerSeries.coeff (R := ℂ) 0 (logKGF α (k + 1))
                =
              PowerSeries.coeff (R := ℂ) 0 (logKGF α k * logGF) := by
                simp [logKGF]
            _ =
              PowerSeries.coeff (R := ℂ) 0 (logKGF α k)
                * PowerSeries.coeff (R := ℂ) 0 logGF := by
                rw [PowerSeries.coeff_mul]
                simp
            _ = logKCoeffℂ α (k + 1) 0 := by
                rw [hlog0, mul_zero]
                simp [logKCoeffℂ, shiftedElemSymmℂ_succ_zero]
      | succ n ihn =>
          have hn1 : ((n : ℂ) + 1) ≠ 0 := by
            intro h
            apply_fun Complex.re at h
            simp at h
            linarith [Nat.cast_nonneg (α := ℝ) n]
          have hGF := coeff_logKGF_succ_recurrence α k n
          rw [ihn, ihk n] at hGF
          have hT := logKCoeffℂ_succ_recurrence α hα k n
          have hgoal :
              ((n : ℂ) + 1) *
                  PowerSeries.coeff (R := ℂ) (n + 1) (logKGF α (k + 1))
                =
              ((n : ℂ) + 1) * logKCoeffℂ α (k + 1) (n + 1) := by
            rw [hGF, hT]
          exact mul_left_cancel₀ hn1 hgoal

end AnalyticCombinatorics
