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

#### STATUS UPDATE (2026-06-13, audit-fix-ch7-trees): convAdd is a genuine WALL for the suggested Gosper route. Precise findings below.

**The Gosper-telescope route suggested above does NOT work.** It was based on the
Mathlib `catalan_eq_centralBinom_div` analogy, but that analogy fails for `β = 3`
(ternary). Verified with sympy `gosper_term`:

  - Catalan summand `centralBinom(k)/(k+1) · centralBinom(n-k)/(n-k+1)`
    IS Gosper-summable (an antidifference hypergeometric term exists) — this is
    *why* Mathlib's `gosperCatalan` certificate exists.
  - The Fuss–Catalan summand `fc s k · fc t (n-k)` (β=3) is **NOT Gosper-summable**:
    `gosper_term` returns `None` both for symbolic `s,t,n` AND for every concrete
    case tested, INCLUDING the specific `fc 1 k · fc 1 (n-k)` (s=t=1) that the
    triple-convolution actually needs.  So there is no `gosperRaney` certificate of
    the assumed "rational multiple of the product" form.  A `gosper_trick` lemma as
    described cannot be stated, let alone proved.

**What convAdd actually is.** It is the *Rothe–Hagen / Raney convolution identity*
(Concrete Mathematics eq. 5.62, generalized; OEIS Fuss–Catalan / Raney numbers):

    ∑_{i+j=n} (s/(3i+s))C(3i+s,i) · (t/(3(n-j)+t))C(3j+t,j) = (s+t)/(3n+s+t)C(3n+s+t,n).

Mathlib has NO support for it (Fuss–Catalan is an explicit TODO in
`Mathlib/Combinatorics/Enumerative/Catalan/Basic.lean`), NO Lagrange inversion
theorem (`PowerSeries/{Substitution,Expand,Inverse}.lean` do not provide it), and
NO Rothe–Hagen/Abel-convolution lemma.

**The remaining viable routes (each a substantial standalone development):**
  1. **Creative telescoping (Zeilberger), induction on n.** The sum `S(s,t,n)`
     provably satisfies the SAME first-order contiguous recurrence as `fc(s+t,n)`:
        (n+1)(2n+u+1)(2n+u+2)·S(s,t,n+1) = (3n+u)(3n+u+1)(3n+u+2)·S(s,t,n), u=s+t.
     With matching base `S(s,t,0)=1=fc(s+t,0)` this closes convAdd by induction on
     n.  Proving the recurrence-for-the-sum requires the Zeilberger certificate
     `R(n,k)` with `L(n)·a(n+1,k) − Rc(n)·a(n,k) = G(n,k+1) − G(n,k)`,
     `a(n,k)=fc s k·fc t(n−k)`, telescoped via `Finset.sum_range_sub`.  The
     certificate is a *genuinely rational* function of k whose denominator spans
     the shifted factors `(3(n−k)+t),(3(n−k)+t+1),(3(n−k)+t+2)` (verified
     numerically: e.g. for s=1,t=2,n=3 the certificate values are −2600/7, −2344/3,
     …, NOT polynomial).  Each telescoped term then needs `Nat.cast_choose` expand +
     `field_simp; ring` with careful nonzero-denominator bookkeeping across BOTH the
     `(3i+s+·)` and `(3(n−i)+t+·)` factor families.  Heavy but mechanical once the
     exact certificate is pinned.
  2. **Lagrange inversion via PowerSeries (from scratch).** Define `B : ℚ⟦X⟧` with
     `B = 1 + X·B^3`; then `fc s n = coeff n (B^s)` and convAdd = `B^s·B^t=B^{s+t}`
     (trivial).  The hard part `coeff n (B^s) = fc s n` is exactly Lagrange
     inversion, which would have to be built (Mathlib lacks it).

**BANKED THIS SESSION (clean-3 [propext, Classical.choice, Quot.sound], green):**
  - `fc_choose_recurrence (s n : ℕ)` in `TernaryFussCatalan.lean`: the Nat-level
    contiguous recurrence
      (n+1)(2n+s+1)(2n+s+2)·C(3n+3+s,n+1) = (3n+3+s)(3n+s+1)(3n+s+2)·C(3n+s,n),
    i.e. the cleared form of `fc s (n+1)/fc s n`.  This is the foundational brick
    for route 1 (it is the per-term recurrence; the sum-level Zeilberger recurrence
    is built on top of it).

**Therefore Part B (ternary counting) is NOT yet a theorem.** `convAdd`,
`ternaryCount_eq_fc_one`, and `ternaryCount_eq_ternaryTreeCount` remain open; the
blocker is the Rothe–Hagen identity, which is a Mathlib-contribution-scale piece of
work, not a quick grind.  Next concrete step: pin the exact Zeilberger certificate
`G(n,k)` symbolically (a CAS with a Zeilberger implementation — Maple/Mathematica,
or `Sigma`/`HolonomicFunctions`; sympy lacks Zeilberger), then formalize route 1.

File:line of the gap: `TernaryFussCatalan.lean` end of file — `convAdd` and the
three closing lemmas (`convAdd`, `ternaryCount_eq_fc_one`,
`ternaryCount_eq_ternaryTreeCount`) are still absent.

---

## PART A — Cayley via Prüfer  (status: object + Fintype + base cases BANKED;
                                Prüfer bijection = remaining hard core)
See /tmp/ac_a_cayley.txt §1,§4.

### Banked (built green, clean-3):  commit 2138aeb
- `LabeledTreeBasic.lean`:
  - `LabeledTree n := {G : SimpleGraph (Fin n) // G.IsTree}`
  - `RootedLabeledTree n := LabeledTree n × Fin n`
  - `Finite`/`Fintype` instances (Fintype.ofFinite — noncomputable, fine)
  - `card_rootedLabeledTree_eq : card (RootedLabeledTree n) = card (LabeledTree n) * n`
- `Cayley.lean`:
  - `labeledTree_zero_isEmpty`, `card_labeledTree_zero : card (LabeledTree 0) = 0`
  - `isTree_bot_fin_one : (⊥ : SimpleGraph (Fin 1)).IsTree`
  - `card_labeledTree_one : card (LabeledTree 1) = 1`
  - `card_rootedLabeledTree_one : card (RootedLabeledTree 1) = 1`

### REMAINING HARD CORE (Part A): the Prüfer bijection for n ≥ 2.
Need (in `Prufer.lean`):
  - `PruferList n := {xs : List (Fin n) // xs.length = n - 2}`
  - `exists_leaf_of_finite_tree` (least leaf of a finite tree on ≥2 vertices)
  - `pruferEncode hn : LabeledTree n → PruferList n` (repeatedly delete least
    leaf, append its neighbor)
  - `pruferDecode hn : PruferList n → LabeledTree n` (standard reconstruction:
    least vertex not in remaining code = next leaf; neighbor = code head)
  - `prufer_decode_encode` / `prufer_encode_decode` (the inverse INVARIANT — the
    genuine hard lemma; see /tmp/ac_a_cayley.txt "Hard core for Cayley")
  - `pruferEquiv hn : LabeledTree n ≃ PruferList n`
Then in `Cayley.lean`:
  - `card_labeledTree_of_two_le : card (LabeledTree n) = n^(n-2)`
    from `Fintype.card_congr pruferEquiv` + `card (PruferList n) = n^(n-2)`
    (PruferList ≃ (Fin (n-2) → Fin n); card = n^(n-2)).
  - `card_labeledTree (1≤n)`, `card_rooted_labeledTree : card (RootedLabeledTree n)
     = n^(n-1)` (from card_rootedLabeledTree_eq + n^(n-2)*n = n^(n-1) for n≥1).
  - CONNECTION: `cayleyRootedTree n = card (RootedLabeledTree n)` for 1≤n
    (cayleyRootedTree n := n^(n-1), so this is card_rooted_labeledTree restated).
    NOTE cayleyRootedTree lives in namespace
    `AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS` (TreeFunction.lean).

Build ONLY via `bash /tmp/acbuild.sh AnalyticCombinatorics.Ch7.SingularityApp.<Module>`
(local lake BANNED).  uisai2 root disk was full; AC-clone `.lake/build` was moved
to `/dev/shm/xhuan5/AC-clone-build` and symlinked (do not delete that symlink).
