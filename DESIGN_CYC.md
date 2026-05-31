# DESIGN: Unlabelled OGF CYC (the last Ch1 construction)

**Goal theorem (faithful, NO `PowerSeries.log` primitive needed):**

For a `CombClass C` with `C.counts 0 = 0` (no size-0 atoms), define the cycle
construction `CYC(C)` = nonempty C-sequences modulo cyclic rotation, as a genuine
graded Fintype class. Prove its OGF:

    CYC(C)(z) = ∑_{d≥1} (φ(d)/d) · mlog( C(z^d) )

where `mlog u := ∑_{j≥1} (1/j)·u^j` (this IS `log(1/(1-u))`; we use its defining
series, sidestepping the missing `PowerSeries.log`), `C(z^d) = subst (X^d) C.ogf`,
and `φ = Nat.totient`. Both sums converge X-adically (each contributes to `[z^n]`
only finitely: `C(z^d)^j` has valuation ≥ `d·j` when `C.counts 0 = 0`) — reuse the
MSET/PSET X-adic `tsum` infrastructure.

## Mathlib pieces CONFIRMED on uisai1 (v4.29.0)
- `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group [Fintype α][∀a,Fintype (fixedBy β a)][Fintype Ω] : (∑ a:α, card (fixedBy β a)) = card Ω * card α`  — **Burnside**, `Ω = orbitRel.Quotient`.
- `MulAction.selfEquivSigmaOrbits'` (orbit decomposition).
- `PowerSeries.coeff_subst_X_pow {k}(hk:k≠0) : coeff n (subst (X^k) f) = if k∣n then algebraMap (coeff (n/k) f) else 0`; `subst_pow`, `constantCoeff_subst_X_pow`.
- `Nat.sum_totient n : n.divisors.sum φ = n`; `Nat.totient`.
- `List.IsRotated` (`~r`), `IsRotated.eqv : Equivalence`, `List.rotate`, `rotate_rotate : (l.rotate n).rotate m = l.rotate (n+m)`, `List.Cycle` (= quotient by rotation), `cyclicPermutations`.
- X-adic tsum infra already in repo (Mset/Pset): `genFun_eq_tprod`, `summable_pow_of_constantCoeff_eq_zero`, `Summable.tsum_eq_zero_add`, `tendsto_iff_coeff_tendsto`.

## Derivation (the math we must formalize)
Grade by number of parts k. `Lk(n)` = length-k lists of components `(m, c)` with
`m≥1`, `c : C.Obj m`, sizes summing to `n`. The group `ℤ/k` (≅ rotations) acts by
`List.rotate`. Burnside over `ℤ/k`:

    #necklaces_k(n) = (1/k) ∑_{i∈ℤ/k} #fixedBy(rotate i on Lk(n)).

`rotate i` and `rotate gcd(i,k)` generate the same cyclic subgroup, so
`fixedBy(rotate i) = fixedBy(rotate gcd(i,k))`. A length-k list fixed by `rotate g`
(`g | k`) is exactly a length-g block repeated `k/g` times ⇒
`#fixedBy(rotate g) = #(length-g lists of size n·g/k) = [z^{ng/k}] C(z)^g` (needs `k/g | n`).
Group `i` by `g = gcd(i,k)`: `#{i∈ℤ/k : gcd(i,k)=g} = φ(k/g)`. Hence

    #necklaces_k(n) = (1/k) ∑_{g|k} φ(k/g) · [z^{ng/k}] C(z)^g.

Sum over k, substitute `k = g·j`:

    CYC_n = ∑_k #necklaces_k(n)
          = ∑_{g≥1} (φ(?)…)  →  [z^n] ∑_{d≥1} (φ(d)/d) ∑_{j≥1} (1/j) C(z^d)^j
          = [z^n] ∑_{d≥1} (φ(d)/d) · mlog(C(z^d)).   ∎

## Layering (one file each, codex writes new files, I wire+audit)
- **L0 `CycModel.lean`**: the component type `Comp C := Σ m:{m//0<m}, C.Obj m`; size; `Lk C n k` = length-k lists summing to n (Fintype); rotation `ℤ/k` action; `cyc` class `Obj n := Σ k∈Icc 1 n, Quotient (rotation on Lk C n k)`; `counts_cyc`.
- **L1 `CycBurnside.lean`** (CRUX): per-k Burnside → `k·#necklaces_k(n) = ∑_{i} #fixedBy`, then fixed-point/period bijection `#fixedBy(rotate g) = card (Lk C (n·g/k) g)` and the `gcd→φ` grouping ⇒ `k·#necklaces_k(n) = ∑_{g|k} φ(k/g)·card(L_g …)`.
- **L2 `CycMlog.lean`**: `mlog`, its X-adic convergence; `[z^n] mlog(C(z^d)) = ∑_{j} (1/j)[z^{n/d}]C(z)^j` when `d|n` (via `coeff_subst_X_pow` + `coeff_pow`).
- **L3 `CycOGF.lean`**: assemble L1+L2 into the headline `ogf_cyc`.

## ROUND 1 CONCLUSIONS (codex, grounded) — supersedes the List model above
**Carrier pivot — use ZMod functions, NOT Lists** (kills List.rotate period theory):
- `CompUpTo C n := Σ m : Fin (n+1), C.Obj m.val`; `compSize` = the `Fin` value. Finite, no global finite component type needed; size bounded by `n`.
- `Word C n k := { f : ZMod k → CompUpTo C n // ∑ x, compSize (f x) = n }` (Fintype, `k>0`).
- Rotation = custom `AddAction (ZMod k)` by right translation `(a +ᵥ f) x = f (x + a)`; sum-constraint preserved by reindexing with `Equiv.addRight a`.
- `necklaces_k C n k := Quotient (AddAction.orbitRel (ZMod k) (Word C n k))`.
- `C.cyc.Obj n := Σ k : {k // 1 ≤ k ∧ k ≤ n}, necklaces_k C n k` (n=0 ⇒ empty). `classical`/`noncomputable`.

**Burnside (additive):** `AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup` ⇒ `(∑ a:ZMod k, card (fixedBy a)) = card(necklaces_k) * k`.

**Corrected index discipline:** `g = gcd(k, a.val)` = block length; `d = k/g = addOrderOf a` = repeat factor & substitution index. Fixed count `= if d ∣ n then card (Word C (n/d) g) else 0`. Reindex `k=g·d`, `1/k=(1/d)(1/g)`, rename block-length `g`→mlog index `j`. **n=0 separately** (don't touch `Nat.divisors 0`).

**Ready-made / confirmed API:** `Nat.totient_div_of_dvd (hnd:d∣n) : φ(n/d) = #{k∈range n | n.gcd k = d}`; `ZMod.addOrderOf_coe (a:ℕ)(n0:n≠0): addOrderOf (a:ZMod n)=n/n.gcd a`; `Function.Periodic.lift` → `α ⧸ AddSubgroup.zmultiples c`; `List.HasPeriod`+`HasPeriod.gcd` (if ever needed); `coeff_subst_X_pow`/`subst_pow`; `Quotient.fintype`; `Fintype.equivFinOfCardEq`.

**THE highest-risk lemma:** `fixedBy_rotation_equiv_word_quotient` — for `a:ZMod k`, fixed `Word C n k` under `+ᵥ a` ≃ words indexed by `ZMod k ⧸ zmultiples a` with total `n / addOrderOf a` (empty when `addOrderOf a ∤ n`). Sub-need: `∑_{x:ZMod k} (lift of quotient fn) = addOrderOf a · ∑_{quotient}`.

## ROUND 2 BLUEPRINT — see HANDOFF/outbox/cyc-r2-reply.md (27 lemmas L0.1–L0.17 / L1.1–L1.4 / L2.1–L2.6, each with Lean stmt + proof strategy + grep-anchored Mathlib).

## ROUND 3 = GO (scratch `lake env lean` exit 0; all names resolve, all signatures elaborate, soundness OK). Corrections baked into implementation:
- Notation: `∑ x ∈ s, …` (not `∑ x in s`).
- `cyc` length index: use finite carrier `(Finset.Icc 1 n : Finset ℕ)` (attach via its coe-sort / `Finset.attach`), NOT `{k//1≤k∧k≤n}` (ℕ-subtype has no auto `Fintype`). All other Fintypes: `classical` + `infer_instance`.
- `WordOn (ι : Type u)` needs explicit universe, omit result-type annotation.
- X-adic: `open scoped PowerSeries.WithPiTopology` + `import Mathlib.Topology.Instances.Rat` (for `TopologicalSpace ℚ`).
- Extra imports: `GroupTheory.QuotientGroup.Defs`, `GroupTheory.Coset.Card`, `Data.ZMod.QuotientGroup`, `NumberTheory.Divisors`, `Data.Fintype.Sigma`.
- `coeff_subst_X_pow` RHS has `algebraMap R S` (here `algebraMap ℚ ℚ = id`, simp away).
- `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup` is a `Nat.card` statement → bridge via `Nat.card_eq_fintype_card`.
- **L2.1 route: DIRECT via `PowerSeries.coeff_pow` + `coeff_ogf`** (prodPow bijection rejected: duplicates work).
- Indexing (confirmed): `g = card(ZMod k ⧸ zmultiples a) = gcd(k,a.val)` = block length; `d = addOrderOf a = k/g` = repeat = subst index; fixed total scales `n → n/d`.

## IMPLEMENTATION LAYERING (split for compile-iteration):
- `CycleModel.lean` (L0): `CompUpTo`/`WordOn`/`Word`/`BlockWord`/`necklaces_k`/`CombClass.cyc` + finite instances + L0.1–L0.17 → ends at `card_fixedBy_rotation`.
- `CycleBurnside.lean` (L1): L1.2–L1.4 → `counts_necklaces_k` (the ℕ identity).
- `CycleOGF.lean` (L2): `mlog`, L2.1 direct, L2.3–L2.6 → headline `CombClass.ogf_cyc`.

## Riskiest steps (want codex's second opinion)
1. **Fixed-point/period bijection** `fixedBy(rotate g on length-k lists) ≃ length-g lists` (block-repeat). Mathlib's rotate-fixed lemmas are thin (`rotate_eq_self_iff_eq_replicate` is period-1 only). Do we build a small period theory, or is there a slicker route (e.g. via `List.Cycle`/`cyclicPermutations` cardinality, or `ZMod k` action with `fixedBy` = `Function.Periodic`)?
2. Cleanest way to realize the `ℤ/k` rotation as a `MulAction` whose `fixedBy`/`orbitRel.Quotient` are `Fintype` (decidability on lists of a Fintype component — use `Classical`, `noncomputable`).
3. Whether to grade-by-k via `Σ k, Quotient …` or avoid the explicit quotient Fintype and DEFINE `counts_cyc` from the orbit count (still a real class? prefer genuine quotient Obj).
4. The `k = g·j` reindex + `1/k = (1/g)(1/j)` and pulling `φ` — cleanest with `Nat.divisorsEquiv`/`Nat.sum_divisorsAntidiagonal` or manual.
