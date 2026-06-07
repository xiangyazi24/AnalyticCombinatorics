import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.KernelBarriers
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernelClose
import AnalyticCombinatorics.Ch8.Partitions.RecordBasics

/-!
# Mass-rate campaign: §8 the record pullback with summable defect (R7 core)

ChatGPT-Pro consult (task 19e127f1) established that the intended record-cover lemmas are NOT
derivable from boundedness + forward-fill + `b(n)→0` alone (explicit slowly-oscillating
countermodel).  The honest route needs the **one-step pullback with a quantitative defect**

  `Δ_N = (|b(N)| + M·|S_N − 1| + M·prefixTail(N)) / μ`,

summable on the `t = √n` scale for the genuine partition kernel.  This file banks the exact
one-step pullback (running-max version).  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

/-- **One-step record pullback (running max), with explicit defect.** -/
theorem exists_window_near_max {a b μ M : ℝ} {N N₀ : ℕ} (hN2 : 2 ≤ N) (hμ : 0 < μ)
    (hMnonneg : 0 ≤ M)
    (hMbound : ∀ k : ℕ, k ≤ N → u k ≤ M)
    (hmax : ∀ k : ℕ, N₀ ≤ k → k ≤ N → u k ≤ u N)
    (hwin : μ ≤ kernelWindow a b N)
    (hprefix : ∀ m : ℕ, m ∈ Finset.Icc 1 (N - 1) → ¬ (N₀ ≤ N - m) → N < 2 * m) :
    ∃ m : ℕ, m ∈ Finset.Icc 1 (N - 1) ∧
      (a * Real.sqrt (N : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (N : ℝ)) ∧
      u N - (|boundaryTerm N| + M * |kernelMass N - 1|
        + M * ((N : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (N : ℝ)))) / μ ≤ u (N - m) := by
  classical
  set s : Finset ℕ := Finset.Icc 1 (N - 1) with hs
  set win : ℕ → Prop := fun m => a * Real.sqrt (N : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (N : ℝ)
    with hwindef
  set R : ℝ := (N : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (N : ℝ)) with hRdef
  have hRnn : 0 ≤ R := by rw [hRdef]; positivity
  set defect : ℝ := |boundaryTerm N| + M * |kernelMass N - 1| + M * R with hdefdef
  have hdefnn : 0 ≤ defect := by
    rw [hdefdef]
    have h1 := abs_nonneg (boundaryTerm N)
    have h2 : 0 ≤ M * |kernelMass N - 1| := mul_nonneg hMnonneg (abs_nonneg _)
    have h3 : 0 ≤ M * R := mul_nonneg hMnonneg hRnn
    linarith
  have hWnn : ∀ m ∈ s, 0 ≤ erdosWeight N m := fun m hm => erdosWeight_nonneg_of_mem hm
  have huN_nn : 0 ≤ u N := (u_pos (show 1 ≤ N by omega)).le
  have huN_le_M : u N ≤ M := hMbound N (le_refl N)
  have hkw : 0 < kernelWindow a b N := lt_of_lt_of_le hμ hwin
  -- window finset nonempty
  set sWin : Finset ℕ := s.filter win with hsWin
  have hsWin_ne : sWin.Nonempty := by
    rw [hsWin, Finset.filter_nonempty_iff]
    by_contra hcon
    push_neg at hcon
    have hz : kernelWindow a b N = 0 := by
      rw [kernelWindow, ← hs]
      exact Finset.sum_eq_zero (fun m hm => if_neg (hcon m hm))
    linarith [hwin]
  obtain ⟨mstar, hmstar_mem, hmstar_max⟩ := Finset.exists_max_image sWin (fun m => u (N - m)) hsWin_ne
  obtain ⟨hmstar_s, hmstar_win⟩ := Finset.mem_filter.mp hmstar_mem
  set v : ℝ := u (N - mstar) with hvdef
  refine ⟨mstar, hmstar_s, hmstar_win, ?_⟩
  have hrec : u N = (∑ m ∈ s, erdosWeight N m * u (N - m)) + boundaryTerm N :=
    u_recurrence N hN2
  -- split the kernel sum into window / complement
  have hsplitsum : (∑ m ∈ s, erdosWeight N m * u (N - m))
      = (∑ m ∈ s, if win m then erdosWeight N m * u (N - m) else 0)
        + (∑ m ∈ s, if win m then 0 else erdosWeight N m * u (N - m)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hw : win m
    · rw [if_pos hw, if_pos hw]; ring
    · rw [if_neg hw, if_neg hw]; ring
  -- window part ≤ v · kernelWindow
  have hwin_part : (∑ m ∈ s, if win m then erdosWeight N m * u (N - m) else 0)
      ≤ v * kernelWindow a b N := by
    rw [kernelWindow, ← hs, Finset.mul_sum]
    refine Finset.sum_le_sum (fun m hm => ?_)
    by_cases hw : win m
    · rw [if_pos hw, if_pos hw]
      have hle : u (N - m) ≤ v := hmstar_max m (Finset.mem_filter.mpr ⟨hm, hw⟩)
      calc erdosWeight N m * u (N - m) ≤ erdosWeight N m * v :=
            mul_le_mul_of_nonneg_left hle (hWnn m hm)
        _ = v * erdosWeight N m := by ring
    · rw [if_neg hw, if_neg hw, mul_zero]
  -- complement part ≤ uN·(mass − window) + M·R
  have hmasswin : kernelMass N - kernelWindow a b N
      = ∑ m ∈ s, if win m then 0 else erdosWeight N m := by
    rw [kernelMass, kernelWindow, ← hs, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hw : win m
    · rw [if_pos hw, if_pos hw]; ring
    · rw [if_neg hw, if_neg hw]; ring
  have hcomp_part : (∑ m ∈ s, if win m then 0 else erdosWeight N m * u (N - m))
      ≤ u N * (kernelMass N - kernelWindow a b N) + M * R := by
    have hbound : ∀ m ∈ s, (if win m then 0 else erdosWeight N m * u (N - m))
        ≤ (if win m then 0 else erdosWeight N m * u N)
          + M * (if N < 2 * m then erdosWeight N m else 0) := by
      intro m hm
      have hMite : 0 ≤ M * (if N < 2 * m then erdosWeight N m else 0) := by
        have hi : (0:ℝ) ≤ (if N < 2 * m then erdosWeight N m else 0) := by
          split_ifs with h; exacts [hWnn m hm, le_rfl]
        exact mul_nonneg hMnonneg hi
      by_cases hw : win m
      · rw [if_pos hw, if_pos hw]; linarith
      · rw [if_neg hw, if_neg hw]
        by_cases hpre : N₀ ≤ N - m
        · have hle : u (N - m) ≤ u N := hmax (N - m) hpre (Nat.sub_le N m)
          nlinarith [mul_le_mul_of_nonneg_left hle (hWnn m hm), hMite]
        · have hN2m : N < 2 * m := hprefix m hm hpre
          rw [if_pos hN2m]
          have hle : u (N - m) ≤ M := hMbound (N - m) (Nat.sub_le N m)
          nlinarith [mul_le_mul_of_nonneg_left hle (hWnn m hm),
            mul_nonneg (hWnn m hm) huN_nn]
    calc (∑ m ∈ s, if win m then 0 else erdosWeight N m * u (N - m))
        ≤ ∑ m ∈ s, ((if win m then 0 else erdosWeight N m * u N)
            + M * (if N < 2 * m then erdosWeight N m else 0)) := Finset.sum_le_sum hbound
      _ = (∑ m ∈ s, if win m then 0 else erdosWeight N m * u N)
            + M * (∑ m ∈ s, if N < 2 * m then erdosWeight N m else 0) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = u N * (kernelMass N - kernelWindow a b N)
            + M * (∑ m ∈ s, if N < 2 * m then erdosWeight N m else 0) := by
          rw [hmasswin]
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          by_cases hw : win m
          · rw [if_pos hw, if_pos hw, mul_zero]
          · rw [if_neg hw, if_neg hw, mul_comm]
      _ ≤ u N * (kernelMass N - kernelWindow a b N) + M * R := by
          have hrh : (∑ m ∈ s, if N < 2 * m then erdosWeight N m else 0) ≤ R := by
            rw [hRdef, hs]; exact right_half_kernel_sum_le N
          have : M * (∑ m ∈ s, if N < 2 * m then erdosWeight N m else 0) ≤ M * R :=
            mul_le_mul_of_nonneg_left hrh hMnonneg
          linarith
  -- combine
  have hrec2 : u N = (∑ m ∈ s, if win m then erdosWeight N m * u (N - m) else 0)
      + (∑ m ∈ s, if win m then 0 else erdosWeight N m * u (N - m)) + boundaryTerm N := by
    rw [hrec, hsplitsum]
  have hbnd : u N ≤ v * kernelWindow a b N + u N * (kernelMass N - kernelWindow a b N) + M * R
      + boundaryTerm N := by
    linarith [hrec2, hwin_part, hcomp_part]
  -- kernelWindow · (uN − v) ≤ defect
  have hkey : kernelWindow a b N * (u N - v) ≤ defect := by
    have hb : boundaryTerm N ≤ |boundaryTerm N| := le_abs_self _
    have huk : u N * (kernelMass N - 1) ≤ M * |kernelMass N - 1| := by
      calc u N * (kernelMass N - 1) ≤ u N * |kernelMass N - 1| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) huN_nn
        _ ≤ M * |kernelMass N - 1| :=
            mul_le_mul_of_nonneg_right huN_le_M (abs_nonneg _)
    have hexp : kernelWindow a b N * (u N - v)
        = u N - (v * kernelWindow a b N + u N * (kernelMass N - kernelWindow a b N))
          + u N * (kernelMass N - 1) := by ring
    rw [hexp, hdefdef]
    linarith [hbnd, hb, huk]
  -- conclude v ≥ uN − defect/μ
  have hdiff : u N - v ≤ defect / μ := by
    rcases le_or_gt (u N - v) 0 with hle | hlt
    · have : (0:ℝ) ≤ defect / μ := by positivity
      linarith
    · rw [le_div_iff₀ hμ]
      have : u N - v ≤ defect / kernelWindow a b N := by
        rw [le_div_iff₀ hkw]; linarith [hkey]
      calc (u N - v) * μ ≤ (defect / kernelWindow a b N) * μ :=
            mul_le_mul_of_nonneg_right this hμ.le
        _ ≤ (defect / μ) * μ := by
            apply mul_le_mul_of_nonneg_right _ hμ.le
            gcongr
        _ = defect := by field_simp
  show u N - defect / μ ≤ v
  linarith [hdiff]

/-- **One-step record pullback (running min), with explicit defect.** -/
theorem exists_window_near_min {a b μ M : ℝ} {N N₀ : ℕ} (hN2 : 2 ≤ N) (hμ : 0 < μ)
    (hMnonneg : 0 ≤ M)
    (hMbound : ∀ k : ℕ, k ≤ N → u k ≤ M)
    (hmin : ∀ k : ℕ, N₀ ≤ k → k ≤ N → u N ≤ u k)
    (hwin : μ ≤ kernelWindow a b N)
    (hprefix : ∀ m : ℕ, m ∈ Finset.Icc 1 (N - 1) → ¬ (N₀ ≤ N - m) → N < 2 * m) :
    ∃ m : ℕ, m ∈ Finset.Icc 1 (N - 1) ∧
      (a * Real.sqrt (N : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (N : ℝ)) ∧
      u (N - m) ≤ u N + (|boundaryTerm N| + M * |kernelMass N - 1|
        + M * ((N : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (N : ℝ)))) / μ := by
  classical
  set s : Finset ℕ := Finset.Icc 1 (N - 1) with hs
  set win : ℕ → Prop := fun m => a * Real.sqrt (N : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (N : ℝ)
    with hwindef
  set R : ℝ := (N : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (N : ℝ)) with hRdef
  have hRnn : 0 ≤ R := by rw [hRdef]; positivity
  set defect : ℝ := |boundaryTerm N| + M * |kernelMass N - 1| + M * R with hdefdef
  have hdefnn : 0 ≤ defect := by
    rw [hdefdef]
    have h1 := abs_nonneg (boundaryTerm N)
    have h2 : 0 ≤ M * |kernelMass N - 1| := mul_nonneg hMnonneg (abs_nonneg _)
    have h3 : 0 ≤ M * R := mul_nonneg hMnonneg hRnn
    linarith
  have hWnn : ∀ m ∈ s, 0 ≤ erdosWeight N m := fun m hm => erdosWeight_nonneg_of_mem hm
  have huN_nn : 0 ≤ u N := (u_pos (show 1 ≤ N by omega)).le
  have huN_le_M : u N ≤ M := hMbound N (le_refl N)
  have hkw : 0 < kernelWindow a b N := lt_of_lt_of_le hμ hwin
  set sWin : Finset ℕ := s.filter win with hsWin
  have hsWin_ne : sWin.Nonempty := by
    rw [hsWin, Finset.filter_nonempty_iff]
    by_contra hcon
    push_neg at hcon
    have hz : kernelWindow a b N = 0 := by
      rw [kernelWindow, ← hs]
      exact Finset.sum_eq_zero (fun m hm => if_neg (hcon m hm))
    linarith [hwin]
  obtain ⟨mstar, hmstar_mem, hmstar_min⟩ := Finset.exists_min_image sWin (fun m => u (N - m)) hsWin_ne
  obtain ⟨hmstar_s, hmstar_win⟩ := Finset.mem_filter.mp hmstar_mem
  set v : ℝ := u (N - mstar) with hvdef
  refine ⟨mstar, hmstar_s, hmstar_win, ?_⟩
  have hrec : u N = (∑ m ∈ s, erdosWeight N m * u (N - m)) + boundaryTerm N :=
    u_recurrence N hN2
  have hsplitsum : (∑ m ∈ s, erdosWeight N m * u (N - m))
      = (∑ m ∈ s, if win m then erdosWeight N m * u (N - m) else 0)
        + (∑ m ∈ s, if win m then 0 else erdosWeight N m * u (N - m)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hw : win m
    · rw [if_pos hw, if_pos hw]; ring
    · rw [if_neg hw, if_neg hw]; ring
  -- window part ≥ v · kernelWindow
  have hwin_part : v * kernelWindow a b N
      ≤ (∑ m ∈ s, if win m then erdosWeight N m * u (N - m) else 0) := by
    rw [kernelWindow, ← hs, Finset.mul_sum]
    refine Finset.sum_le_sum (fun m hm => ?_)
    by_cases hw : win m
    · rw [if_pos hw, if_pos hw]
      have hge : v ≤ u (N - m) := hmstar_min m (Finset.mem_filter.mpr ⟨hm, hw⟩)
      calc v * erdosWeight N m = erdosWeight N m * v := by ring
        _ ≤ erdosWeight N m * u (N - m) := mul_le_mul_of_nonneg_left hge (hWnn m hm)
    · rw [if_neg hw, if_neg hw, mul_zero]
  have hmasswin : kernelMass N - kernelWindow a b N
      = ∑ m ∈ s, if win m then 0 else erdosWeight N m := by
    rw [kernelMass, kernelWindow, ← hs, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hw : win m
    · rw [if_pos hw, if_pos hw]; ring
    · rw [if_neg hw, if_neg hw]; ring
  -- complement part ≥ uN·(mass − window) − M·R
  have hcomp_part : u N * (kernelMass N - kernelWindow a b N) - M * R
      ≤ (∑ m ∈ s, if win m then 0 else erdosWeight N m * u (N - m)) := by
    have hbound : ∀ m ∈ s, (if win m then 0 else erdosWeight N m * u N)
          - M * (if N < 2 * m then erdosWeight N m else 0)
        ≤ (if win m then 0 else erdosWeight N m * u (N - m)) := by
      intro m hm
      have hMite : 0 ≤ M * (if N < 2 * m then erdosWeight N m else 0) := by
        have hi : (0:ℝ) ≤ (if N < 2 * m then erdosWeight N m else 0) := by
          split_ifs with h; exacts [hWnn m hm, le_rfl]
        exact mul_nonneg hMnonneg hi
      by_cases hw : win m
      · rw [if_pos hw, if_pos hw]; linarith
      · rw [if_neg hw, if_neg hw]
        by_cases hpre : N₀ ≤ N - m
        · have hge : u N ≤ u (N - m) := hmin (N - m) hpre (Nat.sub_le N m)
          nlinarith [mul_le_mul_of_nonneg_left hge (hWnn m hm), hMite]
        · have hN2m : N < 2 * m := hprefix m hm hpre
          rw [if_pos hN2m]
          have hmb := Finset.mem_Icc.mp hm
          have hge : 0 ≤ u (N - m) := (u_pos (show 1 ≤ N - m by omega)).le
          nlinarith [mul_nonneg (hWnn m hm) hge, mul_le_mul_of_nonneg_right huN_le_M (hWnn m hm)]
    calc u N * (kernelMass N - kernelWindow a b N) - M * R
        ≤ (∑ m ∈ s, if win m then 0 else erdosWeight N m * u N)
            - M * (∑ m ∈ s, if N < 2 * m then erdosWeight N m else 0) := by
          have heq : (∑ m ∈ s, if win m then 0 else erdosWeight N m * u N)
              = u N * (kernelMass N - kernelWindow a b N) := by
            rw [hmasswin, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun m _ => ?_)
            by_cases hw : win m
            · rw [if_pos hw, if_pos hw, mul_zero]
            · rw [if_neg hw, if_neg hw, mul_comm]
          have hrh : (∑ m ∈ s, if N < 2 * m then erdosWeight N m else 0) ≤ R := by
            rw [hRdef, hs]; exact right_half_kernel_sum_le N
          rw [heq]
          have : M * (∑ m ∈ s, if N < 2 * m then erdosWeight N m else 0) ≤ M * R :=
            mul_le_mul_of_nonneg_left hrh hMnonneg
          linarith
      _ = ∑ m ∈ s, ((if win m then 0 else erdosWeight N m * u N)
            - M * (if N < 2 * m then erdosWeight N m else 0)) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ ≤ (∑ m ∈ s, if win m then 0 else erdosWeight N m * u (N - m)) := Finset.sum_le_sum hbound
  have hrec2 : u N = (∑ m ∈ s, if win m then erdosWeight N m * u (N - m) else 0)
      + (∑ m ∈ s, if win m then 0 else erdosWeight N m * u (N - m)) + boundaryTerm N := by
    rw [hrec, hsplitsum]
  have hbnd : v * kernelWindow a b N + u N * (kernelMass N - kernelWindow a b N) - M * R
      + boundaryTerm N ≤ u N := by
    linarith [hrec2, hwin_part, hcomp_part]
  have hkey : kernelWindow a b N * (v - u N) ≤ defect := by
    have hb : -|boundaryTerm N| ≤ boundaryTerm N := neg_abs_le _
    have huk : -(M * |kernelMass N - 1|) ≤ u N * (kernelMass N - 1) := by
      have h1 : -(u N * |kernelMass N - 1|) ≤ u N * (kernelMass N - 1) := by
        have := mul_le_mul_of_nonneg_left (neg_abs_le (kernelMass N - 1)) huN_nn
        linarith [this]
      have h2 : -(M * |kernelMass N - 1|) ≤ -(u N * |kernelMass N - 1|) := by
        have := mul_le_mul_of_nonneg_right huN_le_M (abs_nonneg (kernelMass N - 1))
        linarith
      linarith
    have hexp : kernelWindow a b N * (v - u N)
        = (v * kernelWindow a b N + u N * (kernelMass N - kernelWindow a b N))
          - u N - u N * (kernelMass N - 1) := by ring
    rw [hexp, hdefdef]
    linarith [hbnd, hb, huk]
  have hdiff : v - u N ≤ defect / μ := by
    rcases le_or_gt (v - u N) 0 with hle | hlt
    · have : (0:ℝ) ≤ defect / μ := by positivity
      linarith
    · rw [le_div_iff₀ hμ]
      have hle2 : v - u N ≤ defect / kernelWindow a b N := by
        rw [le_div_iff₀ hkw]; linarith [hkey]
      calc (v - u N) * μ ≤ (defect / kernelWindow a b N) * μ :=
            mul_le_mul_of_nonneg_right hle2 hμ.le
        _ ≤ (defect / μ) * μ := by
            apply mul_le_mul_of_nonneg_right _ hμ.le
            gcongr
        _ = defect := by field_simp
  show v ≤ u N + defect / μ
  linarith [hdiff]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
