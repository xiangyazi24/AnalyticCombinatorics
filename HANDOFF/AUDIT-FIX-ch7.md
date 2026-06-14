# AUDIT-FIX Ch7 — tree COUNTS as theorems (Cayley + ternary Fuss–Catalan)

Branch: `audit-fix-ch7-trees`.

Goal: replace the by-fiat counts (`cayleyRootedTree n := n^(n-1)`,
`ternaryTreeCount n := C(3n,n)/(2n+1)`) with genuine combinatorial objects whose
cardinality is *proved* equal to the closed form, and connect to the banked
definitions (do NOT redefine them — prove equalities).

---

## PART B — ternary trees  (status: object + recurrence + value-connection BANKED;
                            triple-convolution closed form = remaining hard core)

### Banked (built green, clean-3 [propext, Classical.choice, Quot.sound]):
- `TernaryTreeBasic.lean`: `TernaryTree` (leaf | node t t t), `internalSize`,
  `TernaryTreeOfSize n`, `DecidableEq`.  (commit e02c752)
- `TernaryTreeRecurrence.lean`:
  - `succEquiv n : TernaryTreeOfSize (n+1) ≃ Σ p:TripleIndex n, (subtrees)`
  - `instFintypeTernaryTreeOfSize` (strong recursion on size via succEquiv)
  - `ternaryCount n := Fintype.card (TernaryTreeOfSize n)`
  - `ternaryCount_zero : ternaryCount 0 = 1`
  - `ternaryCount_succ : ternaryCount (n+1) = ∑ p:TripleIndex n,
       ternaryCount p.1 * ternaryCount p.2.1 * ternaryCount p.2.2`
  (commit e02c752)
- `TernaryFussCatalan.lean`:  (commit cf7336f)
  - `fc s n := s/(3n+s) * C(3n+s, n)`  (generalized Fuss–Catalan / Raney rational, ℚ)
  - `key_choose_identity : (2n+1)*C(3n+1,n) = (3n+1)*C(3n,n)`
  - `fc_one_eq_ternary : fc 1 n = C(3n,n)/(2n+1)`
  - `ternaryTreeCount_eq_fc_one : (ternaryTreeCount n : ℚ) = fc 1 n`

### REMAINING HARD CORE (the only missing fact for Part B):
Prove the **binary convolution additivity** of the Raney rationals:

    convAdd : ∀ s t n, ∑ ij ∈ antidiagonal n, fc s ij.1 * fc t ij.2 = fc (s+t) n

(equivalently the triple convolution `∑_{i+j+k=n} fc 1 i·fc 1 j·fc 1 k = fc 3 n`).

Then close Part B by:
  1. `fc 3 n = fc 1 (n+1)`  — pure binomial algebra:
       fc 3 n = 3/(3n+3)·C(3n+3,n) = 1/(n+1)·C(3n+3,n);
       fc 1 (n+1) = 1/(3n+4)·C(3n+4,n+1).
       Identity: (n+1)·C(3n+4,n+1) = (3n+4)·... use Nat.choose_mul_succ_eq /
       choose_succ_right_eq twice.  Verifiable by `field_simp; ring` after
       `Nat.cast_choose`.
  2. `ternaryCount n = fc 1 n` by strong induction:
       base `ternaryCount_zero` + `fc 1 0 = 1`;
       step: rewrite `ternaryCount_succ` over `TripleIndex n` into an
       `antidiagonal`-nested double sum, apply IH (ternaryCount i = fc 1 i for
       i ≤ n), then `∑_{i+j+k=n} fc1 i·fc1 j·fc1 k = (convAdd 1 1)→fc 2,
       (convAdd 2 1)→fc 3 = fc 1 (n+1)`.
  3. `ternaryTreeCount_eq_ternaryCount : ternaryTreeCount n = ternaryCount n`
       from `ternaryTreeCount_eq_fc_one` + step 2 (cast back to ℕ; both are ℕ,
       equal as ℚ ⇒ equal as ℕ via `Nat.cast_injective`).

#### How to prove `convAdd` (Gosper / Raney telescoping)
This is the laborious-but-classical core (Mathlib has NO Fuss–Catalan; it is an
explicit TODO in `Mathlib/Combinatorics/Enumerative/Catalan.lean`).  Mirror the
Mathlib `catalan_eq_centralBinom_div` Gosper proof (`gosperCatalan`,
`gosper_trick`, telescope via `Finset.sum_range_sub`) but for the kernel
`fc s k · fc t (n-k)`.  Concretely:
  - Define a Gosper helper `gosperRaney s t n k : ℚ` (a rational multiple of
    `fc s k · fc t (n-k)`; the certificate is linear-in-k over the product).
  - Prove `gosper_trick : gosperRaney s t (n) (k+1) - gosperRaney s t n k
      = fc s k · fc t (n-k)`  by `Nat.cast_choose`-expand to factorials +
    `field_simp; ring` (the certificate equation is a rational-function identity,
    self-verifying once the right certificate is plugged in).
  - Telescope with `Finset.sum_range_sub`, evaluate endpoints to `fc (s+t) n`.
  The single unknown is the explicit certificate `gosperRaney`; derive it by the
  Gosper algorithm on the term ratio
    `fc s (k+1)/fc s k = (3k+s)/(3k+3+s) · C(3k+3+s,k+1)/C(3k+s,k)`
  (a degree-3 rational in k).  Reference: Raney's lemma / Concrete Mathematics
  eq. (5.62) generalized; the certificate is standard.

File:line of the gap: `TernaryFussCatalan.lean` end of file — add `convAdd`
(currently absent) and the three closing lemmas above.

---

## PART A — Cayley via Prüfer  (status: not yet started in this run; see /tmp/ac_a_cayley.txt §1,§4)
Object `LabeledTree n := {G : SimpleGraph (Fin n) // G.IsTree}`,
`RootedLabeledTree n := LabeledTree n × Fin n`.
Bricks to bank independently: Fintype instances; `exists_leaf_of_finite_tree`;
`pruferEncode`/`pruferDecode`; one inverse direction; `pruferEquiv`;
`card_labeledTree = n^(n-2)` (n≥2; n=1 separate); `card_rooted = n^(n-1)`;
connection `cayleyRootedTree n = card (RootedLabeledTree n)`.
HARD CORE: the decode↔encode inverse invariant.

Build ONLY via `bash /tmp/acbuild.sh AnalyticCombinatorics.Ch7.SingularityApp.<Module>`
(local lake BANNED).  uisai2 root disk was full; AC-clone `.lake/build` was moved
to `/dev/shm/xhuan5/AC-clone-build` and symlinked (do not delete that symlink).
