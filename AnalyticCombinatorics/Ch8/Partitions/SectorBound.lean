import AnalyticCombinatorics.Ch8.Partitions.SectorPoincare

/-!
# Abstract sector bound (renewal route B, Layer-2 nonreversible perturbation)

The abstract sector framework (ChatGPT ac R13/R14) for the nonreversible Green comparison:

* definitions `edgeSign`, `grad`, `Jflow`, `divJ`, `Hcut`, `aK`, `aAnti`, `edgeEnergyOn`, `SectorBound`;
* `sector_bound_from_Hcut_on` — from a Hardy bound on `∑ Hcut²` (`≤ 8BΓ²L²·E_edge`), the cut identity
  `aAnti f g = −∑ Hcut(f)·grad g`, and ellipticity `p·E_edge ≤ aSym`, derive
  `|aAnti f g| ≤ θ·√(aSym f f)·√(aSym g g)` with `θ = √8·√B·Γ·L/p`, via Cauchy–Schwarz
  (`Finset.inner_mul_le_norm_mul_norm`) and `sq_le_sq₀`.

`sector_bound_from_Hcut_on` is fully abstract (it consumes the cut identity and Hardy/ellipticity as
hypotheses), so it is independent of the kernel.  Discharging its hypotheses for the *actual* Erdős
rank-difference kernel — the `erdos_rankdiff_sector_input` with `θ ≤ 1/2` — is the lone genuine
analytic residual (needs a reference measure / cut-flux control; see `DOCTRINE-walls.md` R13).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Signed indicator that edge `e` lies on the oriented path from `x` to `y`. -/
def edgeSign (e x y : ℤ) : ℝ :=
  if x ≤ e ∧ e < y then 1 else if y ≤ e ∧ e < x then -1 else 0

/-- Discrete gradient across edge `e`. -/
def grad (f : ℤ → ℝ) (e : ℤ) : ℝ := f (e + 1) - f e

/-- Antisymmetric flow `π_x K x y − π_y K y x`. -/
def Jflow (π : ℤ → ℝ) (K : ℤ → ℤ → ℝ) (x y : ℤ) : ℝ := π x * K x y - π y * K y x

/-- Divergence of the flow at `x`. -/
def divJ (I : Finset ℤ) (J : ℤ → ℤ → ℝ) (x : ℤ) : ℝ := ∑ y ∈ I, J x y

/-- Weighted cut functional at edge `e`. -/
def Hcut (I : Finset ℤ) (J : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (e : ℤ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x ∈ I, ∑ y ∈ I, J x y * f x * edgeSign e x y

/-- Edge energy over an explicit edge set. -/
def edgeEnergyOn (E : Finset ℤ) (f : ℤ → ℝ) : ℝ := ∑ e ∈ E, (grad f e) ^ 2

/-- Abstract sector condition: `|aAnti f g| ≤ θ·√(aSym f f)·√(aSym g g)`. -/
def SectorBound (aAnti aSym : (ℤ → ℝ) → (ℤ → ℝ) → ℝ) (θ : ℝ) : Prop :=
  ∀ f g, |aAnti f g| ≤ θ * Real.sqrt (aSym f f) * Real.sqrt (aSym g g)

lemma Jflow_skew (π : ℤ → ℝ) (K : ℤ → ℤ → ℝ) (x y : ℤ) :
    Jflow π K y x = - Jflow π K x y := by unfold Jflow; ring

/-- **Sector bound from a Hardy estimate** (Cauchy–Schwarz + ellipticity).  Abstract: consumes the
cut identity `hanti`, the Hardy bound `hH`, and ellipticity `helliptic`. -/
theorem sector_bound_from_Hcut_on
    {a b : ℤ} (B Γ L p : ℝ) (J : ℤ → ℤ → ℝ)
    (aAnti aSym : (ℤ → ℝ) → (ℤ → ℝ) → ℝ)
    (hBnn : 0 ≤ B) (hΓnn : 0 ≤ Γ) (hLnn : 0 ≤ L) (hp : 0 < p)
    (hH : ∀ f, ∑ e ∈ Finset.Icc a (b - 1), (Hcut (Finset.Icc a b) J f e) ^ 2
            ≤ 8 * B * Γ ^ 2 * L ^ 2 * edgeEnergyOn (Finset.Icc a (b - 1)) f)
    (hanti : ∀ f g, aAnti f g
            = - ∑ e ∈ Finset.Icc a (b - 1), Hcut (Finset.Icc a b) J f e * grad g e)
    (helliptic : ∀ f, p * edgeEnergyOn (Finset.Icc a (b - 1)) f ≤ aSym f f)
    (hsym_nonneg : ∀ f, 0 ≤ aSym f f) :
    SectorBound aAnti aSym (Real.sqrt 8 * Real.sqrt B * Γ * L / p) := by
  classical
  intro f g
  set E := Finset.Icc a (b - 1) with hE
  set H : ℤ → ℝ := fun e => Hcut (Finset.Icc a b) J f e with hH'
  set G : ℤ → ℝ := fun e => grad g e with hG'
  have hcs : (∑ e ∈ E, H e * G e) ^ 2 ≤ (∑ e ∈ E, (H e) ^ 2) * (∑ e ∈ E, (G e) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq E H G
  have hHf : ∑ e ∈ E, (H e) ^ 2 ≤ 8 * B * Γ ^ 2 * L ^ 2 * edgeEnergyOn E f := hH f
  have hEg : ∑ e ∈ E, (G e) ^ 2 = edgeEnergyOn E g := rfl
  have hEf_nonneg : 0 ≤ edgeEnergyOn E f :=
    Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have hEg_nonneg : 0 ≤ edgeEnergyOn E g :=
    Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have hAf_nonneg : 0 ≤ aSym f f := hsym_nonneg f
  have hAg_nonneg : 0 ≤ aSym g g := hsym_nonneg g
  have hEf_le : edgeEnergyOn E f ≤ aSym f f / p := by
    rw [le_div_iff₀ hp]; linarith [helliptic f]
  have hEg_le : edgeEnergyOn E g ≤ aSym g g / p := by
    rw [le_div_iff₀ hp]; linarith [helliptic g]
  have hHsum_nonneg : 0 ≤ ∑ e ∈ E, (H e) ^ 2 := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have hsum_sq :
      (∑ e ∈ E, H e * G e) ^ 2 ≤ (8 * B * Γ ^ 2 * L ^ 2 / p ^ 2) * aSym f f * aSym g g := by
    calc (∑ e ∈ E, H e * G e) ^ 2
          ≤ (∑ e ∈ E, (H e) ^ 2) * (∑ e ∈ E, (G e) ^ 2) := hcs
      _ ≤ (8 * B * Γ ^ 2 * L ^ 2 * edgeEnergyOn E f) * edgeEnergyOn E g := by
            rw [hEg]; exact mul_le_mul hHf le_rfl hEg_nonneg
              (le_trans hHsum_nonneg hHf)
      _ ≤ (8 * B * Γ ^ 2 * L ^ 2 * (aSym f f / p)) * (aSym g g / p) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hEf_le (by positivity)) hEg_le
              hEg_nonneg (by positivity)
      _ = (8 * B * Γ ^ 2 * L ^ 2 / p ^ 2) * aSym f f * aSym g g := by
            field_simp
  have hanti_abs_sq :
      |aAnti f g| ^ 2 ≤ (8 * B * Γ ^ 2 * L ^ 2 / p ^ 2) * aSym f f * aSym g g := by
    rw [hanti f g, abs_neg, sq_abs]; exact hsum_sq
  set θ : ℝ := Real.sqrt 8 * Real.sqrt B * Γ * L / p with hθdef
  have hθsq : θ ^ 2 = 8 * B * Γ ^ 2 * L ^ 2 / p ^ 2 := by
    rw [hθdef, div_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8), Real.sq_sqrt hBnn]
  have hrhs_nonneg : 0 ≤ θ * Real.sqrt (aSym f f) * Real.sqrt (aSym g g) := by
    rw [hθdef]; positivity
  apply (sq_le_sq₀ (abs_nonneg _) hrhs_nonneg).mp
  calc |aAnti f g| ^ 2
        ≤ (8 * B * Γ ^ 2 * L ^ 2 / p ^ 2) * aSym f f * aSym g g := hanti_abs_sq
    _ = θ ^ 2 * aSym f f * aSym g g := by rw [hθsq]
    _ = (θ * Real.sqrt (aSym f f) * Real.sqrt (aSym g g)) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hAf_nonneg, Real.sq_sqrt hAg_nonneg]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
