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

/-- Total antisymmetric crossing variation at edge `e`. -/
def crossingTV (I : Finset ℤ) (J : ℤ → ℤ → ℝ) (e : ℤ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x ∈ I, ∑ y ∈ I, |J x y| * |edgeSign e x y|

/-- `x` lies in the `B`-neighborhood of edge `e`. -/
def nearEdge (B : ℕ) (e x : ℤ) : Prop := e - (B : ℤ) ≤ x ∧ x ≤ e + (B : ℤ)

instance (B : ℕ) (e x : ℤ) : Decidable (nearEdge B e x) := by unfold nearEdge; infer_instance

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


/-- `aAnti` reduces to the antisymmetric-flow double sum (the diagonal `πfg` terms cancel; the
residual `K`-terms combine into `Jflow` after an `x↔y` swap). -/
lemma aAnti_eq_J_sum (I : Finset ℤ) (π : ℤ → ℝ) (K : ℤ → ℤ → ℝ) (f g : ℤ → ℝ) :
    aAnti I π K f g = - (1 / 2 : ℝ) * ∑ x ∈ I, ∑ y ∈ I, Jflow π K x y * f x * g y := by
  have expand : ∀ (u v : ℤ → ℝ),
      (∑ x ∈ I, π x * u x * (v x - ∑ y ∈ I, K x y * v y))
        = (∑ x ∈ I, π x * u x * v x) - ∑ x ∈ I, ∑ y ∈ I, π x * K x y * u x * v y := by
    intro u v
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun y _ => by ring)
  have hswap : (∑ x ∈ I, ∑ y ∈ I, π x * K x y * g x * f y)
      = ∑ x ∈ I, ∑ y ∈ I, π y * K y x * f x * g y := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))
  have hdiag : (∑ x ∈ I, π x * f x * g x) = ∑ x ∈ I, π x * g x * f x :=
    Finset.sum_congr rfl (fun x _ => by ring)
  have hJ : (∑ x ∈ I, ∑ y ∈ I, Jflow π K x y * f x * g y)
      = (∑ x ∈ I, ∑ y ∈ I, π x * K x y * f x * g y)
        - ∑ x ∈ I, ∑ y ∈ I, π y * K y x * f x * g y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    unfold Jflow; ring
  unfold aAnti aK
  rw [expand f g, expand g f, hJ, ← hswap, hdiag]
  ring

/-- **Exact antisymmetric cut identity**: `aAnti = −½∑ divJ·f·g − ∑ Hcut(f)·grad g`. -/
lemma aAnti_eq_div_plus_Hcut {a b : ℤ} (hab : a ≤ b) (π : ℤ → ℝ) (K : ℤ → ℤ → ℝ) (f g : ℤ → ℝ) :
    aAnti (Finset.Icc a b) π K f g
      = - (1 / 2 : ℝ) * (∑ x ∈ Finset.Icc a b, divJ (Finset.Icc a b) (Jflow π K) x * f x * g x)
        - ∑ e ∈ Finset.Icc a (b - 1), Hcut (Finset.Icc a b) (Jflow π K) f e * grad g e := by
  rw [aAnti_eq_J_sum]
  have hsplit :
      (∑ x ∈ Finset.Icc a b, ∑ y ∈ Finset.Icc a b, Jflow π K x y * f x * g y)
        = (∑ x ∈ Finset.Icc a b, divJ (Finset.Icc a b) (Jflow π K) x * f x * g x)
          + 2 * ∑ e ∈ Finset.Icc a (b - 1), Hcut (Finset.Icc a b) (Jflow π K) f e * grad g e := by
    have step1 :
        (∑ x ∈ Finset.Icc a b, ∑ y ∈ Finset.Icc a b, Jflow π K x y * f x * g y)
          = (∑ x ∈ Finset.Icc a b, ∑ y ∈ Finset.Icc a b, Jflow π K x y * f x * g x)
            + ∑ x ∈ Finset.Icc a b, ∑ y ∈ Finset.Icc a b, Jflow π K x y * f x * (g y - g x) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun y _ => by ring)
    have step2 :
        (∑ x ∈ Finset.Icc a b, ∑ y ∈ Finset.Icc a b, Jflow π K x y * f x * g x)
          = ∑ x ∈ Finset.Icc a b, divJ (Finset.Icc a b) (Jflow π K) x * f x * g x := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      unfold divJ
      rw [Finset.sum_mul, Finset.sum_mul]
    have hpush : ∀ e : ℤ,
        (∑ x ∈ Finset.Icc a b, ∑ y ∈ Finset.Icc a b,
            Jflow π K x y * f x * (edgeSign e x y * grad g e))
          = (∑ x ∈ Finset.Icc a b, ∑ y ∈ Finset.Icc a b,
              Jflow π K x y * f x * edgeSign e x y) * grad g e := by
      intro e
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun y _ => by ring)
    have step3 :
        (∑ x ∈ Finset.Icc a b, ∑ y ∈ Finset.Icc a b, Jflow π K x y * f x * (g y - g x))
          = 2 * ∑ e ∈ Finset.Icc a (b - 1), Hcut (Finset.Icc a b) (Jflow π K) f e * grad g e := by
      have hsub :
          (∑ x ∈ Finset.Icc a b, ∑ y ∈ Finset.Icc a b, Jflow π K x y * f x * (g y - g x))
            = ∑ x ∈ Finset.Icc a b, ∑ y ∈ Finset.Icc a b, ∑ e ∈ Finset.Icc a (b - 1),
                Jflow π K x y * f x * (edgeSign e x y * grad g e) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        refine Finset.sum_congr rfl (fun y hy => ?_)
        rw [edgeSign_path_sum hab hx hy g, Finset.mul_sum]
      rw [hsub, Finset.sum_congr rfl (fun x _ => Finset.sum_comm), Finset.sum_comm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e he => ?_)
      rw [hpush e]
      unfold Hcut
      ring
    rw [step1, step2, step3]
  rw [hsplit]; ring

/-- Divergence-free corollary: if `div J = 0` on `I`, then `aAnti = −∑ Hcut(f)·grad g`. -/
lemma aAnti_eq_neg_sum_Hcut {a b : ℤ} (hab : a ≤ b) (π : ℤ → ℝ) (K : ℤ → ℤ → ℝ) (f g : ℤ → ℝ)
    (hdiv : ∀ x ∈ Finset.Icc a b, divJ (Finset.Icc a b) (Jflow π K) x = 0) :
    aAnti (Finset.Icc a b) π K f g
      = - ∑ e ∈ Finset.Icc a (b - 1), Hcut (Finset.Icc a b) (Jflow π K) f e * grad g e := by
  rw [aAnti_eq_div_plus_Hcut hab]
  have hzero : (∑ x ∈ Finset.Icc a b, divJ (Finset.Icc a b) (Jflow π K) x * f x * g x) = 0 := by
    refine Finset.sum_eq_zero (fun x hx => ?_)
    rw [hdiv x hx]; ring
  rw [hzero]; ring

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

/-- A jump crossing edge `e` (left→right) of size `≤ B` has its start in the `B`-neighborhood. -/
private lemma nearEdge_of_cross_left {B : ℕ} {e x y : ℤ}
    (hxy : x ≤ e ∧ e < y) (hdist : Int.natAbs (y - x) ≤ B) : nearEdge B e x := by
  obtain ⟨h1, h2⟩ := hxy
  unfold nearEdge; omega

/-- A jump crossing edge `e` (right→left) of size `≤ B` has its start in the `B`-neighborhood. -/
private lemma nearEdge_of_cross_right {B : ℕ} {e x y : ℤ}
    (hyx : y ≤ e ∧ e < x) (hdist : Int.natAbs (y - x) ≤ B) : nearEdge B e x := by
  obtain ⟨h1, h2⟩ := hyx
  unfold nearEdge; omega

/-- At most `2B+1` edges have a fixed point in their `B`-neighborhood. -/
private lemma nearEdge_edge_card_le {a b x : ℤ} (B : ℕ) :
    ((Finset.Icc a (b - 1)).filter (fun e : ℤ => nearEdge B e x)).card ≤ 2 * B + 3 := by
  classical
  have hsub : (Finset.Icc a (b - 1)).filter (fun e : ℤ => nearEdge B e x)
        ⊆ Finset.Icc (x - (B : ℤ)) (x + (B : ℤ)) := by
    intro e he
    rw [Finset.mem_filter] at he
    rw [Finset.mem_Icc]
    rcases he with ⟨_heI, hnear⟩
    unfold nearEdge at hnear
    constructor <;> omega
  have hcard := Finset.card_le_card hsub
  have hcardIcc : (Finset.Icc (x - (B : ℤ)) (x + (B : ℤ))).card = 2 * B + 1 := by
    rw [Int.card_Icc]; omega
  rw [hcardIcc] at hcard
  omega

/-- `|f x| ≤ √(local L²-window)` when `x` is in the window. -/
private lemma abs_le_sqrt_local_l2 {a b e x : ℤ} {B : ℕ} (f : ℤ → ℝ)
    (hx : x ∈ (Finset.Icc a b).filter (fun x : ℤ => nearEdge B e x)) :
    |f x| ≤ Real.sqrt (∑ u ∈ (Finset.Icc a b).filter (fun u : ℤ => nearEdge B e u), f u ^ 2) := by
  classical
  set S : Finset ℤ := (Finset.Icc a b).filter (fun u : ℤ => nearEdge B e u) with hS
  have hS_nonneg : 0 ≤ ∑ u ∈ S, f u ^ 2 := Finset.sum_nonneg (fun u _ => sq_nonneg (f u))
  have hterm : f x ^ 2 ≤ ∑ u ∈ S, f u ^ 2 :=
    Finset.single_le_sum (f := fun u : ℤ => f u ^ 2) (fun u _ => sq_nonneg (f u)) hx
  apply (sq_le_sq₀ (abs_nonneg (f x)) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hS_nonneg]
  exact hterm

/-- **One-edge cut estimate**: `|Hcut(f,e)| ≤ crossingTV(e)·√(local L²-window of f)`. -/
lemma abs_Hcut_le_crossingTV_sqrt_local {a b e : ℤ} {B : ℕ} (J : ℤ → ℤ → ℝ) (f : ℤ → ℝ)
    (he : e ∈ Finset.Icc a (b - 1))
    (hstep : ∀ x ∈ Finset.Icc a b, ∀ y ∈ Finset.Icc a b, J x y ≠ 0 → Int.natAbs (y - x) ≤ B) :
    |Hcut (Finset.Icc a b) J f e|
      ≤ crossingTV (Finset.Icc a b) J e
          * Real.sqrt (∑ x ∈ (Finset.Icc a b).filter (fun x : ℤ => nearEdge B e x), f x ^ 2) := by
  classical
  set I : Finset ℤ := Finset.Icc a b with hI
  set S : Finset ℤ := I.filter (fun x : ℤ => nearEdge B e x) with hSdef
  set R : ℝ := Real.sqrt (∑ x ∈ S, f x ^ 2) with hRdef
  have hterm : ∀ x ∈ I, ∀ y ∈ I,
      |J x y * f x * edgeSign e x y| ≤ |J x y| * |edgeSign e x y| * R := by
    intro x hx y hy
    by_cases hJ : J x y = 0
    · simp [hJ]
    · rw [abs_mul, abs_mul]
      -- goal: |J x y| * |f x| * |edgeSign e x y| ≤ |J x y| * |edgeSign e x y| * R
      by_cases hsgn0 : edgeSign e x y = 0
      · rw [hsgn0]; simp
      · have hxnear : nearEdge B e x := by
          unfold edgeSign at hsgn0
          split_ifs at hsgn0 with h1 h2
          · exact nearEdge_of_cross_left h1 (hstep x hx y hy hJ)
          · exact nearEdge_of_cross_right h2 (hstep x hx y hy hJ)
          · exact absurd rfl hsgn0
        have hxS : x ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hx, hxnear⟩
        have hfx : |f x| ≤ R := by
          rw [hRdef, hSdef]; exact abs_le_sqrt_local_l2 f (by rw [← hSdef]; exact hxS)
        have hJnn : 0 ≤ |J x y| := abs_nonneg _
        have hsnn : 0 ≤ |edgeSign e x y| := abs_nonneg _
        nlinarith [mul_nonneg (mul_nonneg hJnn hsnn) (sub_nonneg.mpr hfx), hfx, hJnn, hsnn]
  have hsum_abs : |∑ x ∈ I, ∑ y ∈ I, J x y * f x * edgeSign e x y|
      ≤ ∑ x ∈ I, ∑ y ∈ I, |J x y| * |edgeSign e x y| * R := by
    calc |∑ x ∈ I, ∑ y ∈ I, J x y * f x * edgeSign e x y|
          ≤ ∑ x ∈ I, |∑ y ∈ I, J x y * f x * edgeSign e x y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ I, ∑ y ∈ I, |J x y * f x * edgeSign e x y| := by
            refine Finset.sum_le_sum (fun x _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ x ∈ I, ∑ y ∈ I, |J x y| * |edgeSign e x y| * R := by
            refine Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => hterm x hx y hy))
  have hfactor : (∑ x ∈ I, ∑ y ∈ I, |J x y| * |edgeSign e x y| * R)
      = (∑ x ∈ I, ∑ y ∈ I, |J x y| * |edgeSign e x y|) * R := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul]
  have hH : |Hcut I J f e| ≤ crossingTV I J e * R := by
    unfold Hcut crossingTV
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc (1 / 2 : ℝ) * |∑ x ∈ I, ∑ y ∈ I, J x y * f x * edgeSign e x y|
          ≤ (1 / 2 : ℝ) * (∑ x ∈ I, ∑ y ∈ I, |J x y| * |edgeSign e x y| * R) :=
            mul_le_mul_of_nonneg_left hsum_abs (by norm_num)
      _ = (1 / 2 : ℝ) * (∑ x ∈ I, ∑ y ∈ I, |J x y| * |edgeSign e x y|) * R := by
            rw [hfactor]; ring
  rw [hRdef, hSdef, hI] at hH ⊢
  exact hH

/-- **Local-window multiplicity**: each point lies in `≤ 2B+3` edge windows. -/
lemma nearEdge_multiplicity_le {a b : ℤ} (B : ℕ) (f : ℤ → ℝ) :
    ∑ e ∈ Finset.Icc a (b - 1),
      ∑ x ∈ (Finset.Icc a b).filter (fun x : ℤ => nearEdge B e x), f x ^ 2
      ≤ ((2 * B + 3 : ℕ) : ℝ) * ∑ x ∈ Finset.Icc a b, f x ^ 2 := by
  classical
  have hinner : ∀ x ∈ Finset.Icc a b,
      (∑ e ∈ Finset.Icc a (b - 1), if nearEdge B e x then f x ^ 2 else 0)
        ≤ ((2 * B + 3 : ℕ) : ℝ) * f x ^ 2 := by
    intro x hx
    have hsum_eq : (∑ e ∈ Finset.Icc a (b - 1), if nearEdge B e x then f x ^ 2 else 0)
        = (((Finset.Icc a (b - 1)).filter (fun e : ℤ => nearEdge B e x)).card : ℝ) * f x ^ 2 := by
      rw [← Finset.sum_filter]; simp [nsmul_eq_mul]
    rw [hsum_eq]
    have hcardR : (((Finset.Icc a (b - 1)).filter (fun e : ℤ => nearEdge B e x)).card : ℝ)
        ≤ ((2 * B + 3 : ℕ) : ℝ) := by exact_mod_cast nearEdge_edge_card_le (a := a) (b := b) (x := x) B
    exact mul_le_mul_of_nonneg_right hcardR (sq_nonneg (f x))
  calc ∑ e ∈ Finset.Icc a (b - 1),
        ∑ x ∈ (Finset.Icc a b).filter (fun x : ℤ => nearEdge B e x), f x ^ 2
        = ∑ e ∈ Finset.Icc a (b - 1), ∑ x ∈ Finset.Icc a b, if nearEdge B e x then f x ^ 2 else 0 := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [Finset.sum_filter]
    _ = ∑ x ∈ Finset.Icc a b, ∑ e ∈ Finset.Icc a (b - 1), if nearEdge B e x then f x ^ 2 else 0 := by
        rw [Finset.sum_comm]
    _ ≤ ∑ x ∈ Finset.Icc a b, ((2 * B + 3 : ℕ) : ℝ) * f x ^ 2 :=
        Finset.sum_le_sum hinner
    _ = ((2 * B + 3 : ℕ) : ℝ) * ∑ x ∈ Finset.Icc a b, f x ^ 2 := by rw [Finset.mul_sum]

/-- **Hardy estimate** `∑ Hcut² ≤ 16BΓ²L²·E_edge` (discharges `sector_bound_from_Hcut_on`'s `hH`).
The energy uses the boundary edge `Icc (a-1) (b-1)` (ac R15 correction: a constant has zero internal
edge energy but nonzero `Hcut`). -/
theorem Hcut_l2_le_boundary {a b : ℤ} (hab : a ≤ b) (B : ℕ) (Γ L : ℝ)
    (J : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (hBpos : 1 ≤ B)
    (hLen : ((b - a + 2 : ℤ).toNat : ℝ) ≤ L) (hbase : f (a - 1) = 0)
    (hstep : ∀ x ∈ Finset.Icc a b, ∀ y ∈ Finset.Icc a b, J x y ≠ 0 → Int.natAbs (y - x) ≤ B)
    (hΓ : ∀ e ∈ Finset.Icc a (b - 1), crossingTV (Finset.Icc a b) J e ≤ Γ) :
    ∑ e ∈ Finset.Icc a (b - 1), (Hcut (Finset.Icc a b) J f e) ^ 2
      ≤ 16 * (B : ℝ) * Γ ^ 2 * L ^ 2 * edgeEnergyOn (Finset.Icc (a - 1) (b - 1)) f := by
  classical
  have hpoint : ∀ e ∈ Finset.Icc a (b - 1),
      (Hcut (Finset.Icc a b) J f e) ^ 2
        ≤ Γ ^ 2 * ∑ x ∈ (Finset.Icc a b).filter (fun x : ℤ => nearEdge B e x), f x ^ 2 := by
    intro e he
    have h1 := abs_Hcut_le_crossingTV_sqrt_local (a := a) (b := b) (e := e) (B := B) J f he hstep
    have hloc_nonneg : 0 ≤ ∑ x ∈ (Finset.Icc a b).filter (fun x : ℤ => nearEdge B e x), f x ^ 2 :=
      Finset.sum_nonneg (fun x _ => sq_nonneg _)
    have habs : |Hcut (Finset.Icc a b) J f e|
        ≤ Γ * Real.sqrt (∑ x ∈ (Finset.Icc a b).filter (fun x : ℤ => nearEdge B e x), f x ^ 2) :=
      le_trans h1 (mul_le_mul_of_nonneg_right (hΓ e he) (Real.sqrt_nonneg _))
    calc (Hcut (Finset.Icc a b) J f e) ^ 2
          = |Hcut (Finset.Icc a b) J f e| ^ 2 := (sq_abs _).symm
      _ ≤ (Γ * Real.sqrt (∑ x ∈ (Finset.Icc a b).filter (fun x : ℤ => nearEdge B e x), f x ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = Γ ^ 2 * ∑ x ∈ (Finset.Icc a b).filter (fun x : ℤ => nearEdge B e x), f x ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hloc_nonneg]
  have hEnn : 0 ≤ edgeEnergyOn (Finset.Icc (a - 1) (b - 1)) f :=
    Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have hpoinc : ∑ x ∈ Finset.Icc a b, f x ^ 2
      ≤ L ^ 2 * edgeEnergyOn (Finset.Icc (a - 1) (b - 1)) f := by
    have h := interval_l2_le_L2_edgeEnergy hab f hbase
    have hE : edgeEnergyOn (Finset.Icc (a - 1) (b - 1)) f
        = ∑ e ∈ Finset.Icc (a - 1) (b - 1), (f (e + 1) - f e) ^ 2 := by
      simp only [edgeEnergyOn, grad]
    rw [hE]
    have hMsq : (((b - a + 2 : ℤ).toNat : ℝ)) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hLen 2
    have hEnn' : 0 ≤ ∑ e ∈ Finset.Icc (a - 1) (b - 1), (f (e + 1) - f e) ^ 2 :=
      Finset.sum_nonneg (fun e _ => sq_nonneg _)
    exact le_trans h (mul_le_mul_of_nonneg_right hMsq hEnn')
  calc ∑ e ∈ Finset.Icc a (b - 1), (Hcut (Finset.Icc a b) J f e) ^ 2
        ≤ ∑ e ∈ Finset.Icc a (b - 1),
            Γ ^ 2 * ∑ x ∈ (Finset.Icc a b).filter (fun x : ℤ => nearEdge B e x), f x ^ 2 :=
        Finset.sum_le_sum hpoint
    _ = Γ ^ 2 * ∑ e ∈ Finset.Icc a (b - 1),
            ∑ x ∈ (Finset.Icc a b).filter (fun x : ℤ => nearEdge B e x), f x ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ Γ ^ 2 * (((2 * B + 3 : ℕ) : ℝ) * ∑ x ∈ Finset.Icc a b, f x ^ 2) :=
        mul_le_mul_of_nonneg_left (nearEdge_multiplicity_le B f) (sq_nonneg Γ)
    _ ≤ Γ ^ 2 * (((2 * B + 3 : ℕ) : ℝ) * (L ^ 2 * edgeEnergyOn (Finset.Icc (a - 1) (b - 1)) f)) := by
        have h23 : (0 : ℝ) ≤ ((2 * B + 3 : ℕ) : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpoinc h23) (sq_nonneg Γ)
    _ ≤ 16 * (B : ℝ) * Γ ^ 2 * L ^ 2 * edgeEnergyOn (Finset.Icc (a - 1) (b - 1)) f := by
        have hB : ((2 * B + 3 : ℕ) : ℝ) ≤ 16 * (B : ℝ) := by
          have : 2 * B + 3 ≤ 16 * B := by omega
          exact_mod_cast this
        have hLE : 0 ≤ L ^ 2 * edgeEnergyOn (Finset.Icc (a - 1) (b - 1)) f :=
          mul_nonneg (sq_nonneg L) hEnn
        calc Γ ^ 2 * (((2 * B + 3 : ℕ) : ℝ) * (L ^ 2 * edgeEnergyOn (Finset.Icc (a - 1) (b - 1)) f))
              ≤ Γ ^ 2 * (16 * (B : ℝ) * (L ^ 2 * edgeEnergyOn (Finset.Icc (a - 1) (b - 1)) f)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB hLE) (sq_nonneg Γ)
          _ = 16 * (B : ℝ) * Γ ^ 2 * L ^ 2 * edgeEnergyOn (Finset.Icc (a - 1) (b - 1)) f := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
