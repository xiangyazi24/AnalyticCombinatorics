# Pre-release audit — AnalyticCombinatorics (honest rebuild)
_Run 2026-06-20 at commit `a22dde4`. Toolchain `leanprover/lean4:v4.29.0`, Mathlib `v4.29.0`._

## Verdict: PASS — clean-3, no integrity escapes

### 1. Axiom sweep (the headline check)
Source: a full from-scratch build of `AnalyticCombinatorics.Ch1.OGF.Audit` (the master audit file,
which `#print axioms` on every headline theorem), rebuilt on uisai2 (`/dev/shm`), **8603 jobs, 0 errors**.

- **622** theorems carry an explicit `#print axioms` verdict.
- **Distinct axioms across all 622:** exactly `{propext, Classical.choice, Quot.sound}`.
- **Outside the clean-3 set:** NONE.
- **Integrity-escape tokens** (`sorryAx`, `ofReduceBool`, `Lean.ofReduceBool`, `trustCompiler`,
  `nativeDecide`) anywhere in the build output: **0**.

This is the discipline the retracted v1.0.0 failed: that tree compiled with no `sorry` but smuggled
`~17k native_decide` (compiler-trust `ofReduceBool`) and projected conclusions out of hypotheses. The
present tree has none of that — every audited theorem reduces to the three standard Lean/Mathlib axioms.

### 2. Repo-wide source grep
- `sorry | admit | native_decide` (whole-word, code lines) across all 419 `.lean` files: **0 real**.
  (Two grep hits are prose only: `Audit.lean` describing the "no `native_decide`" policy, and
  `ErdosUniform.lean` line 7 "admit uniform O(1/√n)".)
- No `^axiom ` declarations (no custom axioms).

### 3. Statement-fidelity spot record (flagship theorems, clean-3 confirmed)
- `partition_log_isEquivalent` — log p(n) ~ π√(2n/3) (elementary; no circle method).
- `erdos_partition_limit_constant` — p(n) ~ exp(π√(2n/3)) / (4n√3) (the sharp constant, unconditional).
- `logK_transfer_theorem_natural_remainder` — general log^k Δ-domain transfer (any k≥1).
- `coeff_thirdOrder_saddle` + instances (involution/Bell/Blocks3/FragmentedPerm) — saddle 3rd order.
- `fussCatalanGeneral_relative_thirdOrder`, `cayleyRootedTree_..._thirdOrder` — singularity-app 3rd order.
- Lagrange inversion, Pólya/cycle-index, Flajolet continued fractions, multivariate Goncharov–Kolchin
  capstone — all clean-3 (per `HANDOFF/AUDIT-WHOLEBOOK.md`, the 2026-06-14 per-chapter adversarial audit).

### 4. Coverage at release
All nine F&S chapters (I–IX) carry their flagship/named theorems clean-3. See
`COVERAGE_AND_OPEN_FRONTIERS.md` for the per-chapter map and the (optional) remaining depth/breadth.
No major named frontier is open.

### Provenance note
The `v1.0.0` tag (2026-05-06, 1284 files) is the **retracted impostor** release (integrity failure,
archived at `archive/impostor-2026-05` / `archive-impostor-2026-05-30`). The forthcoming release is a
clean break built from scratch since 2026-05-30; it should be tagged `v2.0.0` to mark the discontinuity.
