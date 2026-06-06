# Codex task: complete `kernelMass_sub_approx2` (§5 assembly)

Repo: `~/repos/AC-clone` (uisai2), Lean 4.29 + Mathlib master. Verify each lemma with
`lake env lean AnalyticCombinatorics/Ch8/Partitions/<file>.lean` to EXIT 0. **Do NOT touch**
`AnalyticCombinatorics.lean` or `Audit.lean` (the wiring is done by the caller). Create only NEW
content in `AnalyticCombinatorics/Ch8/Partitions/MassRateApprox2.lean` (append) — one writer.
No `sorry`, no `axiom`, no `native_decide`. Namespace `AnalyticCombinatorics.Ch8.Partitions.Erdos`.

## Goal

```lean
theorem kernelMass_sub_approx2 :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      |kernelMass n - kernelMassApprox2 n| ≤ K / (n : ℝ)
```
where `kernelMass n = ∑ m ∈ Finset.Icc 1 (n-1), erdosWeight n m` (KernelBarriers.lean) and
`kernelMassApprox2 n` (MassRateAssembly.lean).

## Already banked (USE THESE — do not reprove)

- `kernelMassApprox2_eq_tsum_model {n} (hn:1≤n) : kernelMassApprox2 n = ∑' m, modelSummand n m`
- `modelSummand n m = if m=0 then 0 else σ(m)·exp(−(λ/√n)·m)·(1/n + m/n² − Cm²/(8n²√n))`,
  `λ = massLam = C/2`, `Sigma.sigmaR`, `C := …` (ErdosKernel.lean), `C_pos`, `massLam_pos`,
  `massLam` (def `C/2`), `sigmaR_nonneg`.
- `erdosWeight_sub_model_le {n m} (hn:1≤n)(hm1:1≤m)(h2m:2*m≤n)(hsmall:4*C*m²≤√n^3) :`
  `|erdosWeight n m − modelSummand n m| ≤ σ(m)·((3C²+5C+2)·exp(−(λ/√n)m)·(m²/n³+m³/(n³√n)+m⁴/n⁴))`
- `model_error_moment_bound : ∃K,0<K ∧ ∀ᶠ n, (3C²+5C+2)·((1/n³)M₂+(1/(n³√n))M₃+(1/n⁴)M₄)(λ/√n) ≤ K/n`
  where `M_r = sigmaMoment r`.
- `sigmaMoment r t = ∑' m, if m=0 then 0 else m^r·σ(m)·exp(−t·m)`; `summable_pow_sigma_geometric`.
- `sigmaMoment_le_power_sharp (r) : ∃K,0≤K ∧ ∀t,0<t→t≤1→ sigmaMoment r t ≤ K/t^{r+2}`.
- Tail infra (ErdosKernelClose.lean): `right_half_kernel_sum_le n : (∑ m∈Icc 1 (n−1), if n<2m then erdosWeight n m else 0) ≤ n³·exp(−(C/10)√n)`;
  `left_half_tail_sum_le_block_majorants n K (hn:0<n)`, `finite_block_majorant_tail_le_shifted_tsum N K`,
  `summable_leftBlockMajorant`, `leftBlockMajorant k = 2·sigmaQuadConst·(k+1)²·exp(−(C/2)k)`,
  `leftBlockMajorant_nonneg`, `erdos_kernel_sum_nonneg`.

## Cutoff

Use `mainCut n := ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊`. Eventually (n ≥ N₀ for explicit N₀):
- `m ≤ mainCut n → 2*m ≤ n` (since `2·n^{2/3} ≤ n ⟺ n ≥ 8`).
- `m ≤ mainCut n → 4*C*(m:ℝ)² ≤ √n^3` (since `(m:ℝ) ≤ n^{2/3}`, `4C·n^{4/3} ≤ n^{3/2} ⟺ 4C ≤ n^{1/6} ⟺ n ≥ (4C)^6`; and `√n^3 = n^{3/2}`).
- `(λ/√n)·mainCut n → ∞`, i.e. `mainCut/√n = n^{1/6} → ∞` — needed for the tails being exp-small.

Real-power lemmas: `Real.rpow_natCast`, `Real.rpow_le_rpow`, `Real.rpow_natCast`, `Nat.floor_le`,
`Nat.le_floor`, `Real.rpow_lt_rpow`, etc. `√n^3 = n^{3/2}` via `Real.sqrt_eq_rpow` + `rpow` arithmetic,
or stay with `√n^3` and use `Real.sq_sqrt`.

## Decomposition

```
kernelMass n − kernelMassApprox2 n
  = (∑_{m∈Icc 1 (mainCut n)} (erdosWeight n m − modelSummand n m))      -- S_main_diff
  + (∑_{m∈Icc (mainCut n + 1) (n−1)} erdosWeight n m)                   -- S_far_erdos
  − (∑'_{m > mainCut n} modelSummand n m)                               -- tail_model
```
(using `kernelMassApprox2_eq_tsum_model` to split `∑' modelSummand` into `Icc 1 (mainCut)` part +
`m > mainCut` tail; the `m=0` term is `0` since `σ(0)=0`).

Then `|·| ≤ |S_main_diff| + |S_far_erdos| + |tail_model|`. Bound each ≤ K/n.

### Brick A — `S_main_diff` ≤ K/n  (the analytic core; all inputs banked)
- `|S_main_diff| ≤ ∑_{Icc 1 mainCut} |erdosWeight − modelSummand|`  (`Finset.abs_sum_le_sum_abs`).
- per term ≤ `errMaj n m := σ(m)·(3C²+5C+2)·exp(−(λ/√n)m)·(m²/n³+m³/(n³√n)+m⁴/n⁴)`
  by `erdosWeight_sub_model_le` (conditions hold for m ≤ mainCut, eventually).
- `∑_{Icc 1 mainCut} errMaj n m = (3C²+5C+2)·[(1/n³)∑g₂ + (1/(n³√n))∑g₃ + (1/n⁴)∑g₄]`,
  `g_r m = σ(m) m^r exp(−(λ/√n)m)`, via `Finset.mul_sum`/`Finset.sum_add_distrib`.
- `∑_{Icc 1 mainCut} g_r m ≤ sigmaMoment r (λ/√n)` via `Finset.sum_le_tsum` (terms ≥0, summable
  `summable_sigma_exp`; for m∈Icc 1 mainCut, m≥1 so `if m=0` is the else branch).
- ⇒ `∑ errMaj ≤ (3C²+5C+2)·[(1/n³)M₂+(1/(n³√n))M₃+(1/n⁴)M₄] ≤ K/n`  via `model_error_moment_bound`.

### Brick B — `S_far_erdos` ≤ K/n  (exp-small far tail)
Split `Icc (mainCut+1) (n−1)` into `n < 2m` (right half) and `2m ≤ n ∧ mainCut < m` (left far).
- right half: `right_half_kernel_sum_le` gives `≤ n³ exp(−(C/10)√n)`, which is `≤ K/n` eventually
  (exp beats poly: `n³·exp(−(C/10)√n)·n → 0`).
- left far (`mainCut < m ≤ n/2`): `mainCut = n^{2/3} > n^{1/6}·√n`, so `m > K·√n` for `K = n^{1/6} → ∞`.
  Use `left_half_tail_sum_le_block_majorants n K` (with the block index `K ≈ mainCut/√n ≈ n^{1/6}`) +
  `finite_block_majorant_tail_le_shifted_tsum` ⇒ `≤ ∑'_j leftBlockMajorant (j + K)`. Bound this
  geometric-quadratic tail `≤ const·K²·exp(−(C/2)K)` (leftBlockMajorant ~ k²e^{−(C/2)k}); with
  `K ≈ n^{1/6}` this is exp-small `≤ K'/n` eventually. (May need a helper:
  `∑'_j (j+K)²·r^{j+K} ≤ poly(K)·r^K` for `r=exp(−C/2)<1`, from
  `summable_pow_mul_geometric_of_norm_lt_one`.)

### Brick C — `tail_model` ≤ K/n  (exp-small model tail)
`tail_model = ∑'_{m > mainCut} modelSummand n m`. Bound:
`|modelSummand n m| ≤ σ(m)·exp(−(λ/√n)m)·(1/n + m/n² + Cm²/(8n²√n))` (triangle on the coefficient).
Tail-extraction: for `m > mainCut`, `exp(−tm) = exp(−tm/2)exp(−tm/2) ≤ exp(−t·mainCut/2)·exp(−tm/2)`,
so `∑'_{m>mainCut} σ(m)m^k exp(−tm) ≤ exp(−t·mainCut/2)·sigmaMoment k (t/2)`.
With `t=λ/√n`, `t·mainCut/2 = (λ/2)·n^{1/6} → ∞` and `sigmaMoment k (t/2) ≤ K_k/(t/2)^{k+2}=poly(n)`,
so `tail_model ≤ poly(n)·exp(−(λ/2)n^{1/6}) ≤ K/n` eventually.
(Helper: `∑'_{m≥M} f m = ∑' f − ∑_{m<M} f` via `Summable.tsum_eq_add_tsum_ite` or
`sum_add_tsum_compl`; or bound `∑'_{m>M} f ≤ ∑' f` and extract the exp factor pointwise then
re-sum with `tsum_le_tsum` against `exp(−tM/2)·(t/2-moment summand)`.)

### Assemble
`kernelMass_sub_approx2`: combine A+B+C with the decomposition identity (prove the decomposition by
`kernelMassApprox2_eq_tsum_model` + `Finset.sum` splitting + `Summable.sum_add_tsum_*`). Take
`K = K_A + K_B + K_C`. Report exactly which lemmas you proved and their EXIT-0 status.
```

---

## UPDATE (Opus): bricks 1-4 BANKED. Remaining = B, C, D only.

Banked & clean-3 on main: `kernelMassApprox2_eq_tsum_model` (1), `model_error_moment_bound` (2),
`erdosWeight_sub_model_le` (3), `main_range_error_le` (4, = Brick A), plus `mainCut_cond` (private),
`modelSummand`, `summable_sigma_exp` (private), `sigmaR_zero` (private). All in MassRateApprox2.lean.

`main_range_error_le : ∃K,0<K ∧ ∀ᶠ n, ∑_{m∈Icc 1 ⌊n^{2/3}⌋} |erdosWeight n m − modelSummand n m| ≤ K/n`.

### Exact assembly (Brick D)
Let `M := ⌊(n:ℝ)^(2/3:ℝ)⌋₊`. Need `M ≤ n-1` eventually (since `n^{2/3} < n`).
- `Summable (modelSummand n)` — from `kernelMassApprox2_eq_tsum_model` route: modelSummand n =
  the three scaled `summable_sigma_exp` summands summed; prove `Summable (modelSummand n)` by
  rewriting modelSummand m = (the combined if-summand) and using `(h0c.add h1c).sub h2c`-style, OR
  directly: modelSummand n m = (if m=0 then 0 else σ·e·(coef)); dominate by summable. (Cleanest: prove
  `Summable (modelSummand n)` once, reuse.)
- `kernelMassApprox2 n = ∑_{m∈Icc 1 M} modelSummand n m + ∑'_k modelSummand n (k + (M+1))`
  via `kernelMassApprox2_eq_tsum_model` + `Summable.sum_add_tsum_nat_add (M+1)` +
  `Finset.range (M+1)` sum = `modelSummand 0 (=0) + ∑_{Icc 1 M}` (`Finset.range_eq_Ico`,
  `Finset.sum_Icc_eq_sum_range` or split off 0; modelSummand n 0 = 0 by `if_pos`).
- `kernelMass n = ∑_{Icc 1 M} erdosWeight n + ∑_{Icc (M+1) (n-1)} erdosWeight n`
  via `Finset.sum_Icc_consecutive` (1 ≤ M+1, M ≤ n-1).
- `kernelMass n − kernelMassApprox2 n = ∑_{Icc 1 M}(erdosWeight − modelSummand)
     + ∑_{Icc (M+1)(n-1)} erdosWeight − ∑'_k modelSummand n (k+(M+1))`.
- `|·| ≤ ∑_{Icc 1 M}|erdosWeight − modelSummand| + ∑_{Icc(M+1)(n-1)} erdosWeight
     + ∑'_k |modelSummand n (k+(M+1))|` (triangle; erdosWeight ≥0 so its |·| drops;
     `erdos_kernel_sum_nonneg` / `sigmaR_nonneg`).
  ≤ K_A/n  +  K_B/n  +  K_C/n.

### Brick B : `∑_{Icc (M+1)(n-1)} erdosWeight n m ≤ K_B/n` eventually
Split each m by `n < 2m` vs `2m ≤ n`:
- `∑ (if n<2m then erdosWeight else 0) ≤ n³ exp(−(C/10)√n)` (`right_half_kernel_sum_le`), and
  `n³ exp(−(C/10)√n) ≤ K/n` eventually (exp beats poly; `n⁴ exp(−(C/10)√n) → 0`).
- left far (`M < m`, `2m ≤ n`): `M = ⌊n^{2/3}⌋ ≥ K_n·√n` with `K_n := ⌊n^{1/6}⌋ → ∞`.
  `left_half_tail_sum_le_block_majorants n K_n` (m ≥ K_n√n ∧ 2m≤n) +
  `finite_block_majorant_tail_le_shifted_tsum` ⇒ `≤ ∑'_j leftBlockMajorant (j+K_n)`.
  Bound `∑'_j leftBlockMajorant (j+K_n) = ∑'_j 2·sigmaQuadConst·(j+K_n+1)²·exp(−(C/2)(j+K_n))`
  `≤ const·(K_n+1)²·exp(−(C/2)K_n)` (geometric-quadratic tail; helper:
  `∑'_j (j+K+1)² r^{j+K} ≤ poly(K)·r^K`, `r=exp(−C/2)`, via
  `summable_pow_mul_geometric_of_norm_lt_one`/`tsum_geometric_*` shifts). With `K_n ≈ n^{1/6}`,
  exp-small `≤ K/n` eventually. NB the threshold: need `M < m → K_n√n ≤ m`, i.e. `K_n√n ≤ M = ⌊n^{2/3}⌋`,
  i.e. `⌊n^{1/6}⌋·√n ≤ ⌊n^{2/3}⌋` (holds since `n^{1/6}·n^{1/2}=n^{2/3}`, modulo floors — eventually).

### Brick C : `∑'_k |modelSummand n (k+(M+1))| ≤ K_C/n` eventually
- `|modelSummand n m| ≤ (if m=0 then 0 else σ(m)·e^{−tm}·(1/n + m/n² + Cm²/(8n²√n)))` (triangle on coef), t=λ/√n.
- tail-extraction helper: for `m ≥ M`, `(m)^k σ e^{−tm} ≤ exp(−(t/2)M)·((m)^k σ e^{−(t/2)m})`
  (since `e^{−tm}=e^{−(t/2)m}e^{−(t/2)m}` and `e^{−(t/2)m} ≤ e^{−(t/2)M}`).
- ⇒ `∑'_k |modelSummand n (k+M+1)| ≤ exp(−(t/2)(M+1))·[(1/n)M₀(t/2)+(1/n²)M₁(t/2)+(C/(8n²√n))M₂(t/2)]`.
  `M_r(t/2) ≤ K/(t/2)^{r+2} = poly(n)`; `exp(−(t/2)(M+1)) = exp(−(λ/2)·(M+1)/√n) ≈ exp(−(λ/2)n^{1/6})`,
  exp-small ⇒ `≤ K_C/n` eventually.
  (Reindex `∑'_k g(k+M+1)` ↔ indicator `∑'_m (if m≤M then 0 else g m)` via
  `Summable.sum_add_tsum_nat_add` or `tsum_le_tsum` directly on the shifted index.)

### exp-beats-poly helper (reused in B and C)
`∀ a>0, ∀ d:ℕ, ∀ᶠ n, (n:ℝ)^d · exp(−a·√n) ≤ 1/n` (or `≤ K/n`). Prove via
`Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`-style or `nat_cube_mul_exp_neg_sqrt_tendsto_zero`
(already in ErdosKernelClose.lean for d=3) generalized; or compose `n^{d+1}exp(−a√n) → 0`.
