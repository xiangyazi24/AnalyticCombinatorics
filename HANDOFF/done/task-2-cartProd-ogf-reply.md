# Task 2 Reply — `cartProd_ogf`

**Status:** done — sorry replaced, `lake build` green (2695 jobs, 0 errors).

## Diff summary

`AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean:145` — replaced `by sorry` with a full proof.

**Strategy (Cauchy convolution via `Finset.card_bij'`):**

1. `ext n; simp only [coeff_ogf, coeff_mul]; simp only [count]` reduces the goal to:
   `((A.cartProd B).level n).card = ∑ p ∈ antidiagonal n, (A.level p.1).card * (B.level p.2).card`

2. Prove the intermediate `hbij`:
   `((A.cartProd B).level n).card = ((Finset.antidiagonal n).sigma (fun p => A.level p.1 ×ˢ B.level p.2)).card`
   via `Finset.card_bij'` with:
   - forward: `(a, b) ↦ ⟨(A.size a, B.size b), (a, b)⟩`
   - backward: `⟨_, (a, b)⟩ ↦ (a, b)`

3. Close with `rw [hbij, Finset.card_sigma]; simp only [Finset.card_product]`.

## Key lessons learned

- **`simp only [level, Set.Finite.mem_toFinset, Set.mem_setOf_eq]` doesn't reduce membership in `cartProd.level`.**
  After `simp only [level]`, the term is `_ ∈ Set.Finite.toFinset _` but `Set.Finite.mem_toFinset` silently fails to apply (unused simp lemma warning). Root cause unclear — possibly a simp pattern matching issue with the `noncomputable` chain.

- **`level_mem_iff` as a simp lemma also fails** (explicit `x` argument, C cannot be inferred from element type alone).

- **Fix:** Use `level_mem_iff` with explicit `C :=` named argument everywhere:
  - `(level_mem_iff (C := A.cartProd B) (a, b)).mp h` — extract size condition from membership
  - `(level_mem_iff (C := A) a).mpr rfl` — prove `a ∈ A.level (A.size a)`
  - `exact` accepts the result because `(A.cartProd B).size (a, b)` and `A.size a + B.size b` are definitionally equal
  - `show A.size a + B.size b = n` after `apply (level_mem_iff (C := A.cartProd B) ...).mpr` works via definitional equality of `cartProd.size`

- **`Finset.mem_sigma`, `Finset.mem_antidiagonal`, `Finset.mem_product` all work fine** in `simp only` context for the sigma finset membership.
