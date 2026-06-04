# General H-admissible saddle-point design

Grounding:

- Existing repo bricks read: `Ch8/SaddlePoint/Assembly.lean`, `GaussianCore.lean`, `ExpStirling.lean`.
- `rg` is not installed on this machine; used `find`/`grep`.
- The structure and theorem statement below were checked with `lake env lean --stdin` against the current repo imports.
- F&S source check: official book site `https://ac.cs.princeton.edu/home/`, Chapter VIII page `https://ac.cs.princeton.edu/80saddle/`.

## A. Structures

Use two layers:

1. `HAdmissible`: analytic function, radius/filter, the F&S functions `a`, `b`, window `δ`, and the two uniform hypotheses.
2. `SaddleSequence`: a chosen sequence `r_n` satisfying `a(r_n)=n`.

Do not put existence/uniqueness/monotonicity of `r_n` into `HAdmissible`. That is a separate saddle-selection problem.

F&S `b` should be pinned as

```text
h(r) = log f(r)
a(r) = r * h'(r)
b(r) = r * a'(r) = r^2 * h''(r) + r * h'(r).
```

Equivalently, where the real derivatives exist and `f(r)>0`,

```text
a(r) = r * f'(r) / f(r)
b(r) = r * d/dr (r * f'(r) / f(r)).
```

For the theorem interface below, `a` and `b` are fields. The derivative equalities should be proved in example-specific verification files or a later `HaymanAB` helper layer. The central/tail theorem only uses `a`, `b`, the saddle equation, and the uniform estimates.

Stdin-checked Lean shape:

```lean
import AnalyticCombinatorics.Ch8.SaddlePoint.GaussianCore
import Mathlib

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- Relative local error after removing the saddle phase and Gaussian. -/
def saddleLocalRatio (f : ℂ → ℂ) (a b : ℝ → ℝ) (r θ : ℝ) : ℂ :=
  (f ((r : ℂ) * Complex.exp (θ * Complex.I)) / f (r : ℂ) *
      Complex.exp (-(a r * θ : ℝ) * Complex.I)) /
    Complex.exp (-(b r * θ ^ 2 / 2 : ℝ))

structure HAdmissible (f : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ) where
  ρ : ℝ≥0∞
  radFilter : Filter ℝ
  a : ℝ → ℝ
  b : ℝ → ℝ
  δ : ℝ → ℝ

  hp : HasFPowerSeriesAt f p 0
  radius_eq : p.radius = ρ
  rad_neBot : radFilter.NeBot
  radius_pos : 0 < ρ

  r_pos : ∀ᶠ (r : ℝ) in radFilter, 0 < r
  inside_radius : ∀ᶠ (r : ℝ) in radFilter, ((r : ℂ) ∈ Metric.eball (0 : ℂ) ρ)
  differentiableOn :
    ∀ᶠ (r : ℝ) in radFilter, DifferentiableOn ℂ f (Metric.closedBall 0 r)

  f_pos : ∀ᶠ (r : ℝ) in radFilter, 0 < (f (r : ℂ)).re
  f_real : ∀ᶠ (r : ℝ) in radFilter, (f (r : ℂ)).im = 0

  b_pos : ∀ᶠ (r : ℝ) in radFilter, 0 < b r
  b_tendsto_atTop : Tendsto b radFilter atTop

  δ_pos : ∀ᶠ (r : ℝ) in radFilter, 0 < δ r
  δ_le_pi : ∀ᶠ (r : ℝ) in radFilter, δ r ≤ Real.pi
  δ_tendsto_zero : Tendsto δ radFilter (𝓝 0)
  δ_sqrt_b_tendsto_atTop :
    Tendsto (fun r => δ r * Real.sqrt (b r)) radFilter atTop

  local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in radFilter, ∀ θ : ℝ, |θ| ≤ δ r →
      ‖saddleLocalRatio f a b r θ - 1‖ ≤ ε

  tail_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in radFilter, ∀ θ : ℝ, δ r ≤ |θ| → |θ| ≤ Real.pi →
      Real.sqrt (b r) *
        ‖f ((r : ℂ) * Complex.exp (θ * Complex.I)) / f (r : ℂ)‖ ≤ ε

structure SaddleSequence {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) where
  r : ℕ → ℝ
  tendsTo : Tendsto r atTop hf.radFilter
  saddle_eq : ∀ᶠ n in atTop, hf.a (r n) = (n : ℝ)

namespace HAdmissible

def B {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) : ℕ → ℝ :=
  fun n => hf.b (hr.r n)

def deltaSeq {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) : ℕ → ℝ :=
  fun n => hf.δ (hr.r n)
```

Notes on `radFilter`:

- Entire functions: `radFilter = atTop`, `ρ = ⊤`.
- Finite radius: use a filter like `𝓝[<] ρReal`, plus fields saying radii are positive and inside the disk.
- This is better than forcing every H-admissible function into `atTop`.

Fields intentionally omitted from the minimal theorem interface:

- `δ^3 * b → 0`. This is useful for verifying examples from Taylor bounds, but not needed once `local_uniform` is assumed.
- Existence/uniqueness of `r_n`.
- Derivative identities for `a,b`; put them in verification helpers.

## B. Deriving `Hcentral`

Let

```lean
B n = hf.b (hr.r n)
Δ n = hf.δ (hr.r n)
```

The target is the existing assembly hypothesis

```lean
Tendsto
  (fun n : ℕ =>
    (Real.sqrt (2 * Real.pi * B n) : ℂ) *
      saddleJc f hr.r Δ n)
  atTop (𝓝 1)
```

Use `central_tendsto_one_of_dominated_of_aestronglyMeasurable` from `GaussianCore.lean`.

Inputs:

1. `hBpos`: compose `hf.b_pos` with `hr.tendsTo`.
2. `hL`: compose `hf.δ_sqrt_b_tendsto_atTop` with `hr.tendsTo`.
3. `Hmeas`: derive from `hf.differentiableOn`; `θ ↦ f(r e^{iθ})` is continuous on each fixed circle, then `Hfun` is an indicator of an interval times a continuous function.
4. `Hpoint`: from `hf.local_uniform`.
5. Dominator:

```lean
D x = 2 * Real.exp (-(x ^ 2) / 2)
```

This is integrable by `integrable_exp_neg_mul_sq` plus constant multiplication.

Pointwise proof:

Fix `x : ℝ`. Since

```lean
Δ n * Real.sqrt (B n) → ∞,
```

eventually

```lean
|x| ≤ Δ n * Real.sqrt (B n).
```

Set

```lean
θ_n = x / Real.sqrt (B n).
```

Using `B n > 0`, the cutoff gives `|θ_n| ≤ Δ n`. Compose `hf.local_uniform` with `hr.tendsTo`, apply it at `θ_n`, and get

```lean
saddleLocalRatio f hf.a hf.b (hr.r n) θ_n → 1.
```

On the same eventual set, `hr.saddle_eq` gives `hf.a (hr.r n) = n`, so

```lean
Hfun f hr.r B Δ n x
  =
Complex.exp (-(x ^ 2) / 2) *
  saddleLocalRatio f hf.a hf.b (hr.r n) θ_n.
```

The Gaussian equality uses

```lean
hf.b (hr.r n) * (x / Real.sqrt (hf.b (hr.r n)))^2 = x^2.
```

Then `Hfun n x → exp (-(x^2)/2)`.

Domination proof:

Use `hf.local_uniform` with `ε = 1`. Eventually, for every central `θ`,

```lean
‖saddleLocalRatio f hf.a hf.b r θ - 1‖ ≤ 1,
```

hence

```lean
‖saddleLocalRatio f hf.a hf.b r θ‖ ≤ 2.
```

For `x` inside the scaled window,

```lean
‖Hfun f hr.r B Δ n x‖
  ≤ 2 * Real.exp (-(x ^ 2) / 2).
```

Outside the window, `Hfun = 0`.

Hard step:

- If `local_uniform` is stated as the relative Gaussian error above, the abstract derivation is bounded: mostly filter composition, cutoff algebra, measurability, and Gaussian domination.
- If the local hypothesis is instead the looser book prose `exp(i aθ - bθ²/2 + o(1))`, or if one wants to derive it from derivative/Taylor hypotheses, this becomes substantial. One then has to formalize the uniform Taylor remainder on a moving window and convert it to the relative-error statement.

So the genuinely hard brick is not DCT itself. It is obtaining the relative `local_uniform` field for nontrivial examples.

## C. Deriving `Htail`

Target:

```lean
Tendsto
  (fun n : ℕ =>
    (Real.sqrt (2 * Real.pi * B n) : ℂ) *
      saddleJt f hr.r Δ n)
  atTop (𝓝 0)
```

Compose `hf.tail_uniform` with `hr.tendsTo`. For `θ` in the two tail arcs,

```lean
Δ n ≤ |θ|,  |θ| ≤ π,
```

so

```lean
Real.sqrt (B n) *
  ‖f ((hr.r n : ℂ) * exp (θ I)) / f (hr.r n : ℂ)‖ → 0
```

uniformly on the tail.

Since the phase has norm `1`,

```lean
‖saddleG f hr.r n θ‖ =
‖f ((hr.r n : ℂ) * exp (θ I)) / f (hr.r n : ℂ)‖.
```

Then

```text
‖Jt_n‖
  ≤ ‖(2π : ℂ)⁻¹‖ * (length left + length right) * sup_tail ‖saddleG‖
  ≤ ‖(2π : ℂ)⁻¹‖ * (2π) * sup_tail ‖saddleG‖.
```

Multiplying by `sqrt(2π B n)` gives a constant times

```text
sqrt(B n) * sup_tail ‖saddleG‖,
```

which tends to `0` by `tail_uniform`. This is much shorter than central; the only Lean work is interval-integral norm bounds and length bookkeeping.

## D. General theorem statement

Stdin-checked statement shape:

```lean
namespace HAdmissible

theorem central_tendsto_one_of_hadmissible
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJc f hr.r (HAdmissible.deltaSeq hf hr) n)
      atTop (𝓝 1) := by
  -- use GaussianCore.central_tendsto_one_of_dominated_of_aestronglyMeasurable
  sorry

theorem tail_tendsto_zero_of_hadmissible
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJt f hr.r (HAdmissible.deltaSeq hf hr) n)
      atTop (𝓝 0) := by
  sorry

theorem coeff_isEquivalent_saddle
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => saddleScale f hr.r (HAdmissible.B hf hr) n) := by
  -- Apply `coeff_isEquivalent_saddle_assembly_of_cauchy` with:
  -- * `r = hr.r`
  -- * `B = HAdmissible.B hf hr`
  -- * `δ = HAdmissible.deltaSeq hf hr`
  -- * `hp = hf.hp`
  -- * r positive: `hf.r_pos` composed with `hr.tendsTo`
  -- * differentiableOn: `hf.differentiableOn` composed with `hr.tendsTo`
  -- * f nonzero: from `hf.f_pos` composed with `hr.tendsTo`
  -- * interval integrability: from differentiability/continuity on circles
  -- * central: `central_tendsto_one_of_hadmissible hf hr`
  -- * tail: `tail_tendsto_zero_of_hadmissible hf hr`
  -- * scale nonzero: `r_pos + f_pos + b_pos`
  sorry
```

The proof should not call a full build. Single-file `lake env lean ...` only.

## E. Feasibility and recommendation

Verdict:

- `tail_uniform → Htail`: bounded, probably short.
- `local_uniform(relative error) → Hcentral`: bounded but nontrivial. Expect real work in filters, exact algebra, measurability, and DCT packaging.
- derivative/log/Taylor hypotheses → `local_uniform`: substantial. This is the real hard brick for Bell, involutions, and later classes.

Given the exp template, the abstract DCT bridge is now worth doing, but only in the thin form above. Do not try to formalize a full book-faithful Hayman verifier with derivative identities, saddle existence, and Taylor remainder automation yet.

Recommendation:

1. Build the thin abstract bridge now:
   - `saddleLocalRatio`
   - `HAdmissible.B`
   - `HAdmissible.deltaSeq`
   - `central_tendsto_one_of_hadmissible`
   - `tail_tendsto_zero_of_hadmissible`
   - `coeff_isEquivalent_saddle`
2. Keep derivative identities for `a,b` outside this theorem.
3. After that, do concrete examples by proving `local_uniform` and `tail_uniform`.

First implementable brick:

```text
central_tendsto_one_of_localUniform
```

with hypotheses explicitly parameterized by `f r a b δ` and `SaddleSequence`, before wrapping it into the full `HAdmissible` structure. This isolates the hardest reusable step and directly reuses `GaussianCore.lean`.

If a smaller first patch is desired, do `tail_tendsto_zero_of_tailUniform` first. It will validate the tail interface, but it will not de-risk the main central proof.
