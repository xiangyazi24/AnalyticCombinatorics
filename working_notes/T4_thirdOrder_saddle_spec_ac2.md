[intro]
I’ll check the current AnalyticCombinatorics repo for the existing saddle/Hayman structure names so the hypothesis fields I propose match the formalization style.

[answer]
Yes: at third order you must strengthen **both** the local central estimate and the tail estimate to the **smaller third-order error scale**. The current second-order layer already has exactly the right architecture: it records `b3`, `b4`, `corrScale`, plus `local_second_L1` and `tail_second_uniform`; the local field compares the scaled central integrand to `saddleSecondPoly`, and the tail field asks for `sqrt(2π b) * E / corrScale → 0`. filecite `HAdmissible` structure already has the saddle window `δ`, positivity, `δ * sqrt b → ∞`, and a first-order tail field.  I’ll write \(B=b(r)\), \(B_j=b_j(r)\), \(L=\delta(r)\sqrt{B}\), and \(\kappa_3(r)=\mathrm{corrScale}_3(r)\). In the classical case \(\kappa_3\sim B^{-2}\).

## Minimal third-order structure fields

The theorem should use a new structure like:

```lean
structure ThirdOrderHAdmissible {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p)
    extends SecondOrderHAdmissible hf where
  b5 : ℝ → ℝ
  b6 : ℝ → ℝ
  corrScale3 : ℝ → ℝ

  corrScale3_pos :
    ∀ᶠ r : ℝ in hf.radFilter, 0 < corrScale3 r

  corrScale3_tendsto_zero :
    Tendsto corrScale3 hf.radFilter (𝓝 0)

  corrScale3_dominates_third :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ r : ℝ in hf.radFilter,
        saddleThirdCorrectionScale hf.b b3 b4 b5 b6 r
          ≤ K * corrScale3 r

  gaussian_window_tail_third :
    Tendsto
      (fun r : ℝ =>
        (1 + (hf.δ r * Real.sqrt (hf.b r)) ^ 12) *
          Real.exp (-((hf.δ r * Real.sqrt (hf.b r)) ^ 2) / 2) /
          corrScale3 r)
      hf.radFilter (𝓝 0)

  local_third_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(hf.δ r * Real.sqrt (hf.b r))..
                 (hf.δ r * Real.sqrt (hf.b r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio f hf.a hf.b r (x / Real.sqrt (hf.b r)) -
              saddleThirdPoly hf.b b3 b4 b5 b6 r x)‖) /
          corrScale3 r)
      hf.radFilter (𝓝 0)

  tail_third_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ r : ℝ in hf.radFilter, 0 ≤ E r) ∧
      Tendsto
        (fun r : ℝ =>
          Real.sqrt (2 * Real.pi * hf.b r) * E r / corrScale3 r)
        hf.radFilter (𝓝 0) ∧
      (∀ᶠ r : ℝ in hf.radFilter, ∀ n : ℕ, ∀ θ : ℝ,
        hf.δ r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt f r n θ‖ ≤ E r)
```

The robust third correction scale should be:

```lean
def saddleThirdCorrectionScale
    (b b3 b4 b5 b6 : ℝ → ℝ) (r : ℝ) : ℝ :=
  |b6 r| / (b r)^3
  + |b3 r * b5 r| / (b r)^4
  + (b4 r)^2 / (b r)^4
  + (b3 r)^2 * |b4 r| / (b r)^5
  + (b3 r)^4 / (b r)^6
```

This avoids relying on cancellation in \(\delta_2\), just as the existing second-order `saddleCorrectionScale` avoids relying on cancellation between \(b_4\) and \(b_3^2\). fileciteturn22file0, the window must be wide enough in Gaussian scale:

\[
L(r)=\delta(r)\sqrt{B}\to\infty.
\]

That is already in `HAdmissible`. fileciteturn23file0to\infty\) alone is not enough. You also need the Gaussian moment truncation error to be negligible at the **third** scale:

\[
\frac{(1+L^{12})e^{-L^2/2}}{\kappa_3(r)}\to0.
\]

The power \(12\) is because the third-order polynomial contains an \(x^{12}\) term from \(U_3^4/24\). This is the purpose of the `gaussian_window_tail_third` field above.

Second, the local Taylor remainder beyond sextic must be small at the third scale. The cleanest Lean field is the direct L¹ condition:

\[
\frac{1}{\kappa_3(r)}
\int_{-L}^{L} e^{-x^2/2}
\left|
R_7\!\left(r,\frac{x}{\sqrt B}\right)
\right|\,dx \to 0.
\]

A concrete sufficient condition is: for \(|\theta|\le\delta(r)\),

\[
|R_7(r,\theta)|\le M_7(r)|\theta|^7
\]

and

\[
\frac{M_7(r)}{B^{7/2}\kappa_3(r)}\to0.
\]

If \(\kappa_3\sim B^{-2}\), this becomes:

\[
M_7(r)=o(B^{3/2}).
\]

In standard Hayman situations where \(b_j(r)=O(B)\) through the needed derivatives, this holds automatically.

For a power window \(\delta=B^{-\alpha}\), assuming \(b_j=O(B)\), the usual constraints are:

\[
\delta\sqrt B\to\infty
\quad\Longleftrightarrow\quad
\alpha<\frac12,
\]

and

\[
B\delta^3\to0
\quad\Longleftrightarrow\quad
\alpha>\frac13.
\]

So any

\[
\frac13<\alpha<\frac12
\]

works. The standard choice

\[
\delta=B^{-2/5}
\]

still works at third order. No tighter window is needed. It gives \(L=B^{1/10}\), so the Gaussian boundary error is exponentially small in \(B^{1/5}\), hence negligible against \(B^{-2}\).

## 2. Minimal `local_third_L1`

Use the same pattern as `local_second_L1`, but replace `saddleSecondPoly` by the full third-order local polynomial and divide by `corrScale3`.

Let

\[
U_3=-i\frac{B_3x^3}{6B^{3/2}},\quad
U_4=\frac{B_4x^4}{24B^2},\quad
U_5=i\frac{B_5x^5}{120B^{5/2}},\quad
U_6=-\frac{B_6x^6}{720B^3}.
\]

Then the local polynomial should be the **grade ≤ 2** exponential truncation:

\[
P_3
=
1
+U_3
+\left(U_4+\frac12U_3^2\right)
+\left(U_5+U_3U_4+\frac16U_3^3\right)
+\left(
U_6+U_3U_5+\frac12U_4^2+\frac12U_3^2U_4+\frac1{24}U_3^4
\right).
\]

Lean-facing:

```lean
def saddleThirdPoly
    (b b3 b4 b5 b6 : ℝ → ℝ) (r x : ℝ) : ℂ :=
  let B : ℂ := (b r : ℂ)
  let sx : ℂ := (Real.sqrt (b r) : ℂ)
  let X : ℂ := (x : ℂ)
  let U3 : ℂ := -Complex.I * ((b3 r : ℂ) / (6 * sx^3)) * X^3
  let U4 : ℂ := ((b4 r : ℂ) / (24 * B^2)) * X^4
  let U5 : ℂ := Complex.I * ((b5 r : ℂ) / (120 * sx^5)) * X^5
  let U6 : ℂ := -((b6 r : ℂ) / (720 * B^3)) * X^6
  1
    + U3
    + (U4 + (1 / 2 : ℂ) * U3^2)
    + (U5 + U3 * U4 + (1 / 6 : ℂ) * U3^3)
    + (U6 + U3 * U5 + (1 / 2 : ℂ) * U4^2
        + (1 / 2 : ℂ) * U3^2 * U4
        + (1 / 24 : ℂ) * U3^4)
```

The corresponding field is:

```lean
local_third_L1 :
  Tendsto
    (fun r : ℝ =>
      (∫ x in -(hf.δ r * Real.sqrt (hf.b r))..
               (hf.δ r * Real.sqrt (hf.b r)),
        ‖Complex.exp (-(x ^ 2) / 2) *
          (saddleLocalRatio f hf.a hf.b r (x / Real.sqrt (hf.b r)) -
            saddleThirdPoly hf.b b3 b4 b5 b6 r x)‖) /
        corrScale3 r)
    hf.radFilter (𝓝 0)
```

This does **not** assume the coefficient asymptotic conclusion. It only asserts a local central-arc approximation of the integrand, exactly like the existing `local_second_L1` field.  the repository’s sign convention in `saddleSecondPoly`, the third correction is:

\[
\delta_2
=
-\frac{b_6}{48B^3}
+\frac{7b_3b_5}{48B^4}
+\frac{35b_4^2}{384B^4}
-\frac{35b_3^2b_4}{64B^5}
+\frac{385b_3^4}{1152B^6}.
\]

The \(b_3b_5\) sign is positive under the existing `-I * b3` cubic convention. The current second polynomial confirms that convention. fileciteturn22file0L17-L23

## 3. Tail bound: yes, strengthen the scale

If the second-order tail field only says

\[
\sqrt{2\pi B}\,E(r)/\kappa_2(r)\to0,
\]

that is **not enough** for third order, because \(\kappa_3\ll\kappa_2\). You need:

\[
\sqrt{2\pi B}\,E(r)/\kappa_3(r)\to0.
\]

So the theorem needs a `tail_third_uniform` field with the same pointwise inequality but the smaller denominator `corrScale3`.

If your concrete tail estimate is exponentially small, then the same analytic estimate will prove both second and third tail fields. But in the abstract Lean structure, the third-order theorem must explicitly ask for negligibility at the third-order scale.

So:

```lean
tail_third_uniform :
  ∃ E : ℝ → ℝ,
    (∀ᶠ r in hf.radFilter, 0 ≤ E r) ∧
    Tendsto
      (fun r => Real.sqrt (2 * Real.pi * hf.b r) * E r / corrScale3 r)
      hf.radFilter (𝓝 0) ∧
    (∀ᶠ r in hf.radFilter, ∀ n θ,
      hf.δ r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt f r n θ‖ ≤ E r)
```

This mirrors the second-order field exactly, but with `corrScale3`. filecite the existing `SaddleSequence` interface, no extra hypothesis is needed: it already requires the exact saddle equation

```lean
hf.a (r n) = (n : ℝ)
```

eventually. fileciteturn23file0 \(a(r_n)-n=\varepsilon_n\), then third order does need a smallness condition. The leftover linear phase is

\[
i\varepsilon_n\theta
=
i\varepsilon_n x/\sqrt B.
\]

Odd terms alone integrate to zero, but cross terms with the cubic produce an even contribution of size roughly

\[
\frac{\varepsilon_n b_3}{B^2}.
\]

So a sufficient abstract condition is:

\[
\frac{|\varepsilon_n b_3|/B^2+\varepsilon_n^2/B}{\kappa_3}\to0.
\]

If \(\kappa_3\sim B^{-2}\) and \(b_3=O(B)\), this requires roughly

\[
\varepsilon_n=o(B^{-1}).
\]

The simplest Lean path is therefore: **do not approximate the saddle**. Keep the exact `saddle_eq` field and avoid this complication entirely.

## Bottom line

The minimal sufficient third-order hypothesis set is:

```lean
b5, b6
corrScale3_pos
corrScale3_tendsto_zero
corrScale3_dominates_third
gaussian_window_tail_third
local_third_L1
tail_third_uniform
```

plus the existing first-order `HAdmissible` and second-order fields.

The standard window \(\delta=B^{-2/5}\) still suffices under \(b_j=O(B)\) through the required remainder bound. The tail field must be strengthened to the third-order scale unless your tail hypothesis is already formulated as super-polynomial/exponential negligibility. The saddle equation needs no higher-order accuracy if it remains exact.
