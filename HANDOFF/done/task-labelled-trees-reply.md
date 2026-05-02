Done.

Created `AnalyticCombinatorics/PartA/Ch2/LabelledTrees.lean`.

Proved:

- `cayleyCount : ℕ → ℕ`, with `cayleyCount 0 = 0` and `cayleyCount n = n^(n-1)` for `0 < n`.
- Native sanity checks:
  - `cayleyCount 1 = 1`
  - `cayleyCount 2 = 2`
  - `cayleyCount 3 = 9`
  - `cayleyCount 4 = 64`
  - `cayleyCount 5 = 625`
- `labelledRootedTreeEgf : PowerSeries ℚ` with coefficient theorem
  `coeff n labelledRootedTreeEgf = (cayleyCount n : ℚ) / n.factorial`.
- Required EGF coefficient identity:
  `cayley_egf_coeff (n : ℕ) (hn : 0 < n)`.
- `cayleyUnrooted : ℕ → ℕ`, with formula `cayleyUnrooted n = n^(n-2)` for `2 ≤ n`.
- Rooted/unrooted relation:
  `cayleyCount n = n * cayleyUnrooted n` for `2 ≤ n`.
- Prüfer-sequence count:
  `Fintype.card (Fin (n - 2) → Fin n) = n^(n-2)`.
- Unrooted/Prüfer relation for `2 ≤ n`.

Verification:

```text
lake build AnalyticCombinatorics.PartA.Ch2.LabelledTrees
Build completed successfully.
```
