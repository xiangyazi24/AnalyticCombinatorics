# AUDIT-FIX Ch9: Feller → uniform-permutation cycle-count bridge

## Audit finding (restated)
`permutationCycles_tendstoInDistribution_gaussian`
(`AnalyticCombinatorics/Ch9/LimitLaws/PermutationCycles.lean:536`) proves the
Gaussian cycle CLT for the random variable `cycleCount n` under the **Feller
coupling** measure `cycleP n = Measure.pi (fun i => cycleBernoulliLaw i)`
(independent `Bernoulli(1/(k+1))`), **not** under the genuine uniform permutation
measure `uniformPermMeasure n`
(`AnalyticCombinatorics/Ch9/LimitLaws/RCyclesPoisson.lean:31`).  The theorem name
over-claims: as stated the Gaussian law is about a sum of independent Bernoullis,
not about the cycle count of a uniform random permutation.

## What is needed to make it FAITHFUL
The equidistribution bridge: the total cycle count of a uniform random
permutation of `Fin n` (the repo's
`RCyclesPoissonNS.totalCycleCount`, `ExpectedCycles.lean:34`,
`= ∑_{r=1}^n rCycleCount n r σ` = number of orbits including fixed points) has the
**same law on `ℕ`** as `cycleCount n` under `cycleP n` (`= ∑_{k=1}^n Bern(1/k)`).
Then transport the existing Feller Gaussian CLT across that `IdentDistrib` to get
`permutationCycles_gaussian_uniformPerm` on `uniformPermMeasure`.

Both laws have the same probability generating function
`E[x^{Ncyc}] = ∏_{k=1}^n (x+k-1)/k = x^{(n)}/n!` (rising factorial / n!).
The Feller side is easy (independence + the Bernoulli pgf `((k-1)+x)/k`, already
implicit in `cycleCount_charFun`, `PermutationCycles.lean:156`).
The uniform side is the real content: the **rising-factorial cycle-count identity**

  `∑_{σ : Perm (Fin n)} x^{numC σ} = ∏_{k=0}^{n-1} (x + k)`,

equivalently `#{σ : Perm (Fin n) // numC σ = j} = stirlingFirst n j` (unsigned
Stirling number of the first kind).

## VERIFIED PROGRESS (banked, clean-3, 0 sorry)
New file `AnalyticCombinatorics/Ch9/LimitLaws/PermCycleCountBridge.lean`
(wired into root `AnalyticCombinatorics.lean`).  It develops `numC σ`
(number of orbits `= (#α − #support σ) + #cycleType σ`) and the inductive engine
of the rising-factorial identity via `Equiv.Perm.decomposeOption`
(`Perm (Option α) ≃ Option α × Perm α`):

- `optionCongr_eq_extendDomain` : `σ.optionCongr = σ.extendDomain (someSub α)`
  (lets us reuse Mathlib's `extendDomain` cycle lemmas).
- `cycleType_optionCongr` : `cycleType σ.optionCongr = cycleType σ`.
- `support_card_optionCongr` : `#support σ.optionCongr = #support σ`.
- `numC_optionCongr` : `numC (σ.optionCongr) = numC σ + 1`
  — the **none-fixed half** of the recursion (`decomposeOption.symm (none, σ)`):
  adjoining `none` as a new fixed point adds exactly one cycle.  This is the
  leading-`x` factor of the recursion
  `∑_{Perm (Option α)} x^{numC} = (x + #α)·∑_{Perm α} x^{numC}`.
- `cycleType_swap_mul_of_both_fixed` : if `τ z = z`, `τ y = y`, `z ≠ y` then
  `cycleType (swap z y * τ) = {2} + cycleType τ`
  — the **fixed-point splice subcase** (inserted `none` lands on a fixed point
  `some a`, `σ a = a`): the two singletons merge into a 2-cycle, orbit count
  unchanged.

## THE WALL (precise: file:line + missing fact)
Two genuinely hard pieces remain; Mathlib provides no leverage for either.

### Wall 1 — splice/merge, nontrivial-cycle subcase (the crux)
**Missing fact:** for `τ : Perm α`, `z` a fixed point of `τ` (`τ z = z`) and
`y ∈ τ.support` (so `τ y ≠ y`), with `z ≠ y`:
`cycleType (swap z y * τ)` is `τ.cycleType` with the cycle through `y`
(length `ℓ`) replaced by one of length `ℓ + 1`; consequently
`numC (swap z y * τ) = numC τ` (the singleton `{z}` is spliced into `y`'s cycle,
orbit count preserved).

This requires proving `IsCycle (swap z y * c)` where `c := τ.cycleOf y` is a
cycle, `y ∈ c.support`, `z ∉ c.support` — i.e. inserting an outside element `z`
into a cycle `c` yields a cycle of length `#c.support + 1`.  Mathlib has only the
opposite direction `Equiv.Perm.IsCycle.swap_mul`
(`Mathlib/GroupTheory/Perm/Cycle/Basic.lean:428`,
`IsCycle (swap x (f x) * f)` for `f x ≠ x`, `f (f x) ≠ x` — this *splits*, with
`x` already in the cycle), and the low-level `isCycle_swap_mul_aux₁/₂`
(`Basic.lean:368,387`).  The converse / insertion direction is NOT in Mathlib and
must be built from `isCycle_swap_mul_aux₂` (estimated ~100+ lines), then combined
with `Disjoint.cycleType_mul` to peel `c` off `τ`.

Searched and absent in Mathlib (`v4.29.0_8a178386`):
- no `cycleType`/`support`/`IsCycle` lemma for `swap _ _ * σ` keyed on `SameCycle`;
- no cycle-count merge/split lemma (`numC (swap x y * σ) = numC σ ± 1`);
- no cycle-structure lemmas for `optionCongr` / `removeNone` / `decomposeOption`.

### Wall 2 — rising-factorial identity + IdentDistrib + transport
Even granting Wall 1, the remaining assembly is substantial:
1. Combine `numC_optionCongr`, `cycleType_swap_mul_of_both_fixed`, and Wall 1
   over `decomposeOption` (case-split on `σ none = none` vs `σ none = some a`,
   and within the latter on `σ a = a`) to get the recursion
   `∑_{Perm (Option α)} x^{numC} = (x + #α)·∑_{Perm α} x^{numC}`,
   then induct to `∑_{Perm (Fin n)} x^{numC} = ∏_{k=0}^{n-1}(x+k)` (in `ℂ`).
   NB also needs `numC σ = totalCycleCount n σ` for `σ : Perm (Fin n)`
   (orbit count = `∑_r rCycleCount`; provable from `cycleType` + fixed points).
2. From the rising-factorial identity in `ℂ` with `x = exp(i s)`, compute
   `charFun ((uniformPermMeasure n).map (totalCycleCount n)) s = ∏ cycleBase`
   matching `cycleCount_charFun` (`PermutationCycles.lean:156`).
3. Equal char functions ⟹ equal laws on `ℝ`/`ℕ` (`Measure.ext_of_charFun`),
   giving `IdentDistrib (cycleCount n) (totalCycleCount n) (cycleP n)
   (uniformPermMeasure n)`.  (Mathlib has `MeasureTheory.tendstoInDistribution_of_identDistrib`
   and `TendstoInDistribution.congr`; the transport itself is then short —
   the structure's `tendsto` field is identical once the per-`n` pushforward
   measures agree.)
4. Conclude `permutationCycles_gaussian_uniformPerm` on `uniformPermMeasure`.

## STATUS
Route confirmed sound; foundation + 3 of the recursion's pieces banked
(clean-3, 0 sorry, build green).  The cycle-insertion `IsCycle` lemma (Wall 1)
is the irreducible hard core absent from Mathlib; it gates the full faithful
bridge.  Until it is proved, the Gaussian cycle CLT remains formally about the
Feller coupling `cycleP`, not `uniformPermMeasure` — the audit naming finding
stands (NOT yet upgraded to FAITHFUL).

Build/audit: `bash /tmp/acbuild.sh AnalyticCombinatorics.Ch9.LimitLaws.PermCycleCountBridge`
→ "Build completed successfully"; all four new theorems
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.
