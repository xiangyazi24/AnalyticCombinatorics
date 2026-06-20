## 1. Saddle equation and `b₂,…,b₆`

Let

```text
g(z) = z / (1 - z),
D := z d/dz,
s := 1 - r.
```

The saddle equation is

```text
D g(r) = r g'(r) = r / (1-r)^2 = r / s^2 = n.
```

For `k ≥ 1`,

```text
b_k = D^k g(r)
    = ∑_{j=1}^k S(k,j) r^j g^{(j)}(r)
    = ∑_{j=1}^k S(k,j) r^j * j! / (1-r)^(j+1).
```

Explicitly:

```text
b₁ = r / s² = n

b₂ = r(1+r) / s³

b₃ = r(1 + 4r + r²) / s⁴

b₄ = r(1+r)(1 + 10r + r²) / s⁵

b₅ = r(1 + 26r + 66r² + 26r³ + r⁴) / s⁶

b₆ = r(1+r)(1 + 56r + 246r² + 56r³ + r⁴) / s⁷
```

Thus

```text
b = b₂ = r(1+r)/s³.
```

As `r → 1⁻`, i.e. `s → 0⁺`,

```text
b₂ ~ 2 / s³,
b₃ ~ 6 / s⁴,
b₄ ~ 24 / s⁵,
b₅ ~ 120 / s⁶,
b₆ ~ 720 / s⁷.
```

Since

```text
n = r/s² ~ 1/s²,
```

we also have

```text
b = b₂ ~ 2 n^(3/2).
```

---

## 2. `δ₂` for this family

The universal formula is

```text
δ₂ =
  - b₆/(48b³)
  + 7b₃b₅/(48b⁴)
  + 35b₄²/(384b⁴)
  - 35b₃²b₄/(64b⁵)
  + 385b₃⁴/(1152b⁶).
```

Substituting the exact `b_k` above and simplifying gives

```text
δ₂ =
  (r - 1)²
  * (r⁸ + 4r⁷ + 28r⁶ - 524r⁵ + 442r⁴
      - 524r³ + 28r² + 4r + 1)
  / (288 r² (1+r)^6).
```

Since `s = 1-r`, this is

```text
δ₂ =
  s²
  * (r⁸ + 4r⁷ + 28r⁶ - 524r⁵ + 442r⁴
      - 524r³ + 28r² + 4r + 1)
  / (288 r² (1+r)^6).
```

At `r=1`, the polynomial numerator is

```text
1 + 4 + 28 - 524 + 442 - 524 + 28 + 4 + 1 = -540,
```

and the denominator is

```text
288 * 1² * 2⁶ = 18432.
```

Therefore

```text
δ₂ ~ -540 / 18432 * s²
    = -15/512 * s².
```

Since `s² ~ 1/n`,

```text
δ₂ ~ -15 / (512 n).
```

For comparison, the second correction is

```text
δ₁ =
  b₄/(8b²) - 5b₃²/(24b³)
  =
  (r - 1)(r⁴ + 2r³ + 12r² + 2r + 1)
  / (12 r (1+r)^3),
```

so

```text
δ₁ ~ -3s/16 ~ -3/(16√n).
```

Thus the expansion hierarchy here is

```text
1 + O(s) + O(s²) + O(s³) + ...
```

not

```text
1 + O(b⁻¹) + O(b⁻²) + ...
```

because for this finite-radius family the higher cumulants satisfy

```text
b_k ~ k! s^(-(k+1)),
```

not `b_k = O(b)`.

---

## 3. Finite-radius third-order local window

The natural Gaussian scale is

```text
1 / √b ~ s^(3/2).
```

The singularity is at angular distance about

```text
s = 1-r.
```

So the saddle window must satisfy

```text
s^(3/2) << δ_n << s.
```

For a robust third-order proof using uniform Taylor remainder bounds through order `6`, choose for example

```text
δ_n = s^(29/20).
```

More invariantly, take

```text
δ_n = s^α
```

with

```text
10/7 < α < 3/2.
```

Why these inequalities:

```text
√b δ_n → ∞
```

is equivalent to

```text
s^(-3/2) * s^α → ∞,
```

so

```text
α < 3/2.
```

Also

```text
δ_n / s → 0
```

requires

```text
α > 1.
```

For a crude uniform seventh-order Taylor remainder,

```text
R₇(θ) = O(s^(-8) |θ|^7).
```

To make this uniformly `o(s²)` on `|θ| ≤ δ_n`, require

```text
s^(-8) δ_n^7 = o(s²),
```

i.e.

```text
δ_n^7 = o(s^10),
```

so

```text
α > 10/7.
```

This also implies the perturbation is uniformly small, since

```text
b₃ δ_n^3 = O(s^(-4) δ_n^3) = o(1)
```

because `α > 4/3`, and `10/7 > 4/3`.

So a clean Lean-friendly condition set is:

```lean
-- with s n = 1 - r n
(h_window_gauss : Tendsto (fun n => Real.sqrt (b n) * δ n) atTop atTop)
(h_window_sing  : Tendsto (fun n => δ n / s n) atTop (𝓝 0))
(h_taylor7      : (fun n => (s n)^(-8 : ℤ) * (δ n)^7)
                    =o[atTop] fun n => (s n)^2)
```

For the concrete choice:

```text
δ_n = s^(29/20)
```

these hold.

Important correction: if by “`o(b⁻²)`” you literally mean

```text
o(b⁻²) = o(s^6),
```

then order-six Taylor data is not enough. The third correction for this family is itself of order

```text
s² ~ n⁻¹,
```

not `b⁻² ~ s⁶`. The correct third-order remainder target is

```text
o(s²)
```

after including `δ₂`, or `O(s³)` if you also want the next scale.

---

## 4. Tail bound

For this finite-radius function, the tail is still exponentially small relative to the saddle contribution, but the proof should use the exact finite-radius real-part drop.

For `z = r e^{iθ}`,

```text
Re g(r) - Re g(r e^{iθ})
=
r(1+r)(1 - cos θ)
/
((1-r) * (1 - 2r cos θ + r²)).
```

With `s = 1-r`, the denominator is

```text
1 - 2r cos θ + r² = s² + 2r(1 - cos θ).
```

Thus

```text
Re g(r) - Re g(r e^{iθ})
=
r(1+r)(1 - cos θ)
/
(s * (s² + 2r(1 - cos θ))).
```

This gives two regimes.

For the near tail

```text
δ_n ≤ |θ| ≤ c s,
```

we have

```text
1 - cos θ ≍ θ²,
s² + 2r(1 - cos θ) ≍ s²,
```

so

```text
Re g(r) - Re g(r e^{iθ}) ≥ C θ² / s³ = C b θ².
```

Therefore the near-tail ratio is bounded by

```text
exp(-C b δ_n²).
```

For the far tail

```text
c s ≤ |θ| ≤ π,
```

the same exact formula gives

```text
Re g(r) - Re g(r e^{iθ}) ≥ C / s,
```

so the far-tail ratio is bounded by

```text
exp(-C / s).
```

Hence the full tail ratio is

```text
O(exp(-C b δ_n²) + exp(-C/s)).
```

For `δ_n = s^α` with `α < 3/2`,

```text
b δ_n² ~ s^(-3) * s^(2α) = s^(-(3 - 2α)) → ∞.
```

Thus

```text
exp(-C b δ_n²)
```

is smaller than every power of `s`, and so is `exp(-C/s)`.

So for third order you want the tail field to expose the exponential bound, not merely the second-order conclusion.

Lean-structure field:

```lean
(h_tail :
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ᶠ n in atTop,
      tailRatio n ≤
        C * (Real.exp (-c * b n * (δ n)^2)
             + Real.exp (-c / s n)))
```

Then derive:

```lean
tailRatio = o[atTop] fun n => (s n)^2
```

or even

```lean
tailRatio = o[atTop] fun n => (s n)^K
```

for any fixed `K`.

If your existing second-order tail lemma only states something like

```lean
tailRatio = o[atTop] fun n => s n
```

then it does **not** automatically extend by “dividing by the smaller third-order scale.” You need either the exponential bound above or a new theorem proving the stronger `o(s²)` consequence.

---

## 5. Subtlety from `r → 1⁻`

The key subtlety is the separation of three scales:

```text
Gaussian width       ~ s^(3/2)
saddle window δ_n    ~ s^α,  10/7 < α < 3/2
singularity distance ~ s
```

So

```text
s^(3/2) << δ_n << s.
```

This means:

1. The local window contains the whole Gaussian mass.
2. The local window remains much smaller than the distance to the singularity.
3. Taylor expansion constants are controlled by powers of `s⁻¹`.
4. The tail starts far enough out that `exp(-C b δ_n²)` kills it.

This is the finite-radius replacement for the entire-function condition where one often takes

```text
δ_n = b^(-2/5).
```

Here

```text
b^(-2/5) ~ s^(6/5),
```

which is valid for a second-order proof, but for a simple uniform third-order Taylor remainder it is not strong enough, because

```text
s^(-8) * (s^(6/5))^7 = s^(2/5),
```

not `o(s²)`.

For third order, take a narrower but still Gaussian-large window, e.g.

```text
δ_n = s^(29/20).
```

---

## 6. Minimal sufficient Lean structure fields

A compact third-order finite-radius saddle structure could have fields like:

```lean
structure FiniteRadiusSaddleThird where
  r : ℕ → ℝ
  s : ℕ → ℝ
  b : ℕ → ℝ
  δ : ℕ → ℝ

  h_s_def : ∀ᶠ n in atTop, s n = 1 - r n
  h_s_pos : ∀ᶠ n in atTop, 0 < s n
  h_s_tendsto : Tendsto s atTop (𝓝 0)

  h_b_asymp : (fun n => b n) ~[atTop] (fun n => 2 * (s n)^(-3 : ℤ))

  h_window_gauss :
    Tendsto (fun n => Real.sqrt (b n) * δ n) atTop atTop

  h_window_sing :
    Tendsto (fun n => δ n / s n) atTop (𝓝 0)

  h_window_remainder7 :
    (fun n => (s n)^(-8 : ℤ) * (δ n)^7)
      =o[atTop] fun n => (s n)^2

  h_local_quad :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n in atTop,
        ∀ θ, |θ| ≤ δ n →
          Real.re (localPhase n θ - localPhase n 0)
            ≤ - c * b n * θ^2

  h_deriv3 :
    b3 n = r n * (1 + 4*r n + (r n)^2) / (s n)^4

  h_deriv4 :
    b4 n = r n * (1+r n) * (1 + 10*r n + (r n)^2) / (s n)^5

  h_deriv5 :
    b5 n =
      r n
      * (1 + 26*r n + 66*(r n)^2 + 26*(r n)^3 + (r n)^4)
      / (s n)^6

  h_deriv6 :
    b6 n =
      r n * (1+r n)
      * (1 + 56*r n + 246*(r n)^2 + 56*(r n)^3 + (r n)^4)
      / (s n)^7

  h_local_third_L1 :
    -- after θ = x / sqrt(b), the local integral equals
    -- Gaussian expectation of exp(W3+...+W6)
    -- up to o(s^2)
    localThirdError =o[atTop] fun n => (s n)^2

  h_tail :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ᶠ n in atTop,
        tailRatio n ≤
          C * (Real.exp (-c * b n * (δ n)^2)
               + Real.exp (-c / s n))
```

You may replace explicit `h_deriv3`–`h_deriv6` by a single field:

```lean
h_deriv_bound :
  ∀ k ∈ Finset.Icc 3 7,
    bDeriv k n = O(s n ^ (-(k+1)))
```

plus exact formulas for `3..6`.

The essential third-order fields are:

```text
√b δ → ∞,
δ/s → 0,
s⁻⁸ δ⁷ = o(s²),
tailRatio ≤ C(exp(-c bδ²)+exp(-c/s)).
```

These are sufficient and do not assume the conclusion.
