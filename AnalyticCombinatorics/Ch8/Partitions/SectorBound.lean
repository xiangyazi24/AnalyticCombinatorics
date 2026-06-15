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

/-- The (non-symmetric) bilinear form `⟨f, π·(I−K)g⟩`. -/
def aK (I : Finset ℤ) (π : ℤ → ℝ) (K : ℤ → ℤ → ℝ) (f g : ℤ → ℝ) : ℝ :=
  ∑ x ∈ I, π x * f x * (g x - ∑ y ∈ I, K x y * g y)

/-- Antisymmetric part of `aK`. -/
def aAnti (I : Finset ℤ) (π : ℤ → ℝ) (K : ℤ → ℤ → ℝ) (f g : ℤ → ℝ) : ℝ :=
  (aK I π K f g - aK I π K g f) / 2

/-- Edge energy over an explicit edge set. -/
def edgeEnergyOn (E : Finset ℤ) (f : ℤ → ℝ) : ℝ := ∑ e ∈ E, (grad f e) ^ 2

/-- Abstract sector condition: `|aAnti f g| ≤ θ·√(aSym f f)·√(aSym g g)`. -/
def SectorBound (aAnti aSym : (ℤ → ℝ) → (ℤ → ℝ) → ℝ) (θ : ℝ) : Prop :=
  ∀ f g, |aAnti f g| ≤ θ * Real.sqrt (aSym f f) * Real.sqrt (aSym g g)

lemma Jflow_skew (π : ℤ → ℝ) (K : ℤ → ℤ → ℝ) (x y : ℤ) :
    Jflow π K y x = - Jflow π K x y := by unfold Jflow; ring

/-- Telescoping identity for gradients on an integer interval (`Int.le_induction` + top-element peel). -/
lemma sum_Icc_grad_of_le {x y : ℤ} (hxy : x ≤ y) (g : ℤ → ℝ) :
    (∑ e ∈ Finset.Icc x (y - 1), grad g e) = g y - g x := by
  induction y, hxy using Int.le_induction with
  | base =>
      have hempty : Finset.Icc x (x - 1) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty]; simp
  | succ y hxy ih =>
      have hins : Finset.Icc x (y + 1 - 1) = insert y (Finset.Icc x (y - 1)) := by
        ext e; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have hy_notin : y ∉ Finset.Icc x (y - 1) := by simp only [Finset.mem_Icc]; omega
      rw [hins, Finset.sum_insert hy_notin, ih]
      unfold grad; ring

/-- **Signed path-sum identity**: the oriented edge-sign sum over `Icc a (b-1)` collapses to the
path from `x` to `y`. -/
lemma edgeSign_path_sum {a b x y : ℤ} (hab : a ≤ b)
    (hx : x ∈ Finset.Icc a b) (hy : y ∈ Finset.Icc a b) (g : ℤ → ℝ) :
    g y - g x = ∑ e ∈ Finset.Icc a (b - 1), edgeSign e x y * grad g e := by
  classical
  have hxa : a ≤ x := (Finset.mem_Icc.mp hx).1
  have hxb : x ≤ b := (Finset.mem_Icc.mp hx).2
  have hya : a ≤ y := (Finset.mem_Icc.mp hy).1
  have hyb : y ≤ b := (Finset.mem_Icc.mp hy).2
  by_cases hxy : x ≤ y
  · have hfilter :
        (Finset.Icc a (b - 1)).filter (fun e : ℤ => x ≤ e ∧ e < y) = Finset.Icc x (y - 1) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hae, heb⟩, hxe, hey⟩; exact ⟨hxe, by omega⟩
      · rintro ⟨hxe, hey⟩; exact ⟨⟨by omega, by omega⟩, hxe, by omega⟩
    calc g y - g x = ∑ e ∈ Finset.Icc x (y - 1), grad g e := by rw [sum_Icc_grad_of_le hxy g]
      _ = ∑ e ∈ (Finset.Icc a (b - 1)).filter (fun e : ℤ => x ≤ e ∧ e < y), grad g e := by
          rw [hfilter]
      _ = ∑ e ∈ Finset.Icc a (b - 1), (if x ≤ e ∧ e < y then grad g e else 0) := by
          rw [Finset.sum_filter]
      _ = ∑ e ∈ Finset.Icc a (b - 1), edgeSign e x y * grad g e := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hpos : x ≤ e ∧ e < y
          · simp [edgeSign, hpos]
          · have hneg : ¬ (y ≤ e ∧ e < x) := by omega
            simp [edgeSign, hpos, hneg]
  · have hyx : y ≤ x := by omega
    have hfilter :
        (Finset.Icc a (b - 1)).filter (fun e : ℤ => y ≤ e ∧ e < x) = Finset.Icc y (x - 1) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hae, heb⟩, hye, hex⟩; exact ⟨hye, by omega⟩
      · rintro ⟨hye, hex⟩; exact ⟨⟨by omega, by omega⟩, hye, by omega⟩
    calc g y - g x = - (g x - g y) := by ring
      _ = - (∑ e ∈ Finset.Icc y (x - 1), grad g e) := by rw [sum_Icc_grad_of_le hyx g]
      _ = ∑ e ∈ Finset.Icc y (x - 1), - grad g e := by rw [Finset.sum_neg_distrib]
      _ = ∑ e ∈ (Finset.Icc a (b - 1)).filter (fun e : ℤ => y ≤ e ∧ e < x), - grad g e := by
          rw [hfilter]
      _ = ∑ e ∈ Finset.Icc a (b - 1), (if y ≤ e ∧ e < x then - grad g e else 0) := by
          rw [Finset.sum_filter]
      _ = ∑ e ∈ Finset.Icc a (b - 1), edgeSign e x y * grad g e := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hneg : y ≤ e ∧ e < x
          · have hpos : ¬ (x ≤ e ∧ e < y) := by omega
            simp [edgeSign, hpos, hneg]
          · have hpos : ¬ (x ≤ e ∧ e < y) := by omega
            simp [edgeSign, hpos, hneg]


/- The exact cut identity `aAnti = −½∑ divJ·f·g − ∑ Hcut(f)·grad g` (discharging `hanti`)
and the Hardy estimate `Hcut_l2_le` (discharging `hH`) are the remaining connective steps;
ChatGPT ac/ac2 R15/R16 gave proof sketches needing Mathlib-shape adaptation. The genuine wall
is the kernel-specific `erdos_rankdiff_sector_input` (see DOCTRINE-walls.md R13). -/

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
