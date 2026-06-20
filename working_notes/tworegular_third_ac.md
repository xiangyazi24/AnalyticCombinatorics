Let

```text
f(z) = C(z) (1-z)^(-1/2),
C(z) = exp(-z/2 - z²/4).
```

Set

```text
t = 1 - z.
```

Then

```text
z = 1 - t
```

and

```text
-z/2 - z²/4
= -(1-t)/2 - (1-2t+t²)/4
= -3/4 + t - t²/4.
```

So

```text
C(z)
= e^(-3/4) exp(t - t²/4)
= e^(-3/4) * (1 + t + t²/4 + O(t³)).
```

Thus the local expansion is

```text
C(z) = γ₀ + γ₁(1-z) + γ₂(1-z)² + O((1-z)³),
```

with

```text
γ₀ = e^(-3/4),
γ₁ = e^(-3/4),
γ₂ = e^(-3/4) / 4.
```

Equivalently, in terms of derivatives at `1`,

```text
γ₀ = C(1),
γ₁ = -C'(1),
γ₂ = C''(1)/2.
```

For this `C`,

```text
C(1) = e^(-3/4),
C'(1) = -e^(-3/4),
C''(1) = e^(-3/4)/2.
```

---

## Coefficient expansions used

We need

```text
[z^n](1-z)^(-1/2),
[z^n](1-z)^(1/2),
[z^n](1-z)^(3/2).
```

The required asymptotics are:

```text
[z^n](1-z)^(-1/2)
=
1/√π * n^(-1/2)
  * (1 - 1/(8n) + 1/(128n²) + O(n^-3)).
```

```text
[z^n](1-z)^(1/2)
=
-1/(2√π) * n^(-3/2)
  -3/(16√π) * n^(-5/2)
  + O(n^(-7/2)).
```

```text
[z^n](1-z)^(3/2)
=
3/(4√π) * n^(-5/2)
  + O(n^(-7/2)).
```

Therefore

```text
[z^n] f(z)
=
γ₀ [z^n](1-z)^(-1/2)
+ γ₁ [z^n](1-z)^(1/2)
+ γ₂ [z^n](1-z)^(3/2)
+ O(n^(-7/2)).
```

Collecting powers gives

```text
[z^n] f(z)
=
n^(-1/2) * (a₀ + a₁/n + a₂/n²)
+ o(n^(-5/2)),
```

where, in terms of `γ₀, γ₁, γ₂`,

```text
a₀ = γ₀ / √π,
```

```text
a₁ = (-γ₀/8 - γ₁/2) / √π,
```

```text
a₂ = (γ₀/128 - 3γ₁/16 + 3γ₂/4) / √π.
```

In terms of derivatives of `C` at `1`:

```text
a₀ = C(1) / √π,
```

```text
a₁ = (C'(1)/2 - C(1)/8) / √π,
```

```text
a₂ = (C(1)/128 + 3C'(1)/16 + 3C''(1)/8) / √π.
```

Substituting

```text
C(1) = e^(-3/4),
C'(1) = -e^(-3/4),
C''(1) = e^(-3/4)/2,
```

we get

```text
a₀ = e^(-3/4) / √π,
```

```text
a₁ = -5 e^(-3/4) / (8√π),
```

```text
a₂ = e^(-3/4) / (128√π).
```

So the final expansion is

```text
[z^n] e^{-z/2-z²/4} (1-z)^(-1/2)
=
e^(-3/4) / √π * n^(-1/2)
- 5e^(-3/4) / (8√π) * n^(-3/2)
+ e^(-3/4) / (128√π) * n^(-5/2)
+ o(n^(-5/2)).
```

Equivalently,

```text
[z^n] f(z)
=
e^(-3/4) / √π * n^(-1/2)
  * (1 - 5/(8n) + 1/(128n²) + o(n^-2)).
```

Numerically,

```text
a₀ ≈ 0.26650428867284237,
a₁ ≈ -0.16656518042052648,
a₂ ≈ 0.002082064755256581.
```
