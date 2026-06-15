import AnalyticCombinatorics.Ch8.Partitions.QVTelescope

/-!
# Green comparison primitives (renewal route B, Layer-2 wall decomposition)

ChatGPT ac R10 broke the lone analytic wall (finite-interval Green/Harnack comparison) into a staged
program.  This file banks the *entrywise* (Neumann-series) layer, which is elementary and useful as
infrastructure:

* `distPow_mono` — monotonicity of the `t`-step law in the kernel: `0 ≤ B ≤ A` entrywise (and
  `μ₀ ≥ 0`) ⟹ `distPow B μ₀ t ≤ distPow A μ₀ t` pointwise.
* `green_neumann_mono` — the finite Green operators are monotone: `∑_{t<T} Bᵗδ_x ≤ ∑_{t<T} Aᵗδ_x`.

ac R10's verdict: entrywise domination alone gives only an `O(1)` Green bound (the local `±1`
minorant is sub-stochastic, mass `2p<1`); the `Θ(L)` finite-interval bound needs the Dirichlet-form /
sector route on top.  This file is the honest infrastructure layer underneath that.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Monotonicity of the `t`-step law in the kernel.**  If `0 ≤ B x y ≤ A x y` entrywise and
`μ₀ ≥ 0`, then `distPow B μ₀ t y ≤ distPow A μ₀ t y` for every `t, y`. -/
lemma distPow_mono (A B : α → α → ℝ) (μ0 : α → ℝ)
    (hBnn : ∀ x y, 0 ≤ B x y) (hμ0nn : ∀ x, 0 ≤ μ0 x)
    (hBA : ∀ x y, B x y ≤ A x y) :
    ∀ t y, distPow B μ0 t y ≤ distPow A μ0 t y := by
  intro t
  induction t with
  | zero => intro y; exact le_refl _
  | succ t ih =>
      intro y
      simp only [distPow]
      refine Finset.sum_le_sum (fun x _ => ?_)
      have hbnn : 0 ≤ distPow B μ0 t x := distPow_nonneg B μ0 hBnn hμ0nn t x
      exact mul_le_mul (ih x) (hBA x y) (hBnn x y) (le_trans hbnn (ih x))

/-- **Entrywise Neumann/Green monotonicity.**  For `0 ≤ B ≤ A` entrywise, the finite Green operators
(partial Neumann sums of the `t`-step laws from a point mass) are monotone in the kernel. -/
lemma green_neumann_mono (A B : α → α → ℝ)
    (hBnn : ∀ x y, 0 ≤ B x y) (hBA : ∀ x y, B x y ≤ A x y) :
    ∀ (T : ℕ) (x y : α),
      (∑ t ∈ Finset.range T, distPow B (fun z => if z = x then (1 : ℝ) else 0) t y)
        ≤ ∑ t ∈ Finset.range T, distPow A (fun z => if z = x then (1 : ℝ) else 0) t y := by
  intro T x y
  refine Finset.sum_le_sum (fun t _ => ?_)
  exact distPow_mono A B _ hBnn (fun z => by split <;> norm_num) hBA t y

end AnalyticCombinatorics.Ch8.Partitions.Erdos
