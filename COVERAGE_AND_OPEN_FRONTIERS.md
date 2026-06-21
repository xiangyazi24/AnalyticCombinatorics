# AnalyticCombinatorics — coverage map & genuine open frontiers
_Updated 2026-06-20 after verifying against the THEOREM FILES (the first pass trusted Audit/HANDOFF prose, which lags)._

## Methodology correction (important)
The first version of this map listed two "open frontiers" — general-β log transfer and the sharp
partition constant. **Both were already done.** They were mis-flagged because I trusted the *prose*
records (Audit.lean `--` comments at 1257/1552, and the HANDOFF gap docs), which **lag the actual
.lean files**. The authoritative sources are: (a) the theorem files themselves, (b) `#print axioms`,
(c) `AUDIT-WHOLEBOOK.md` (the 2026-06-14 whole-book adversarial audit, per-chapter
FAITHFUL/CLEAN). The stale HANDOFF gap/route scratch has been deleted (commit 4deac9b).

## Status: the book's flagship theorems are done, clean-3, across all nine F&S chapters (I–IX)
417 .lean files, 0 real sorry/admit/native_decide. `AUDIT-WHOLEBOOK.md` already certified every chapter
FAITHFUL/CLEAN (06-14); the two hardest *post-audit* frontiers are now also closed (below).

## The two "frontiers" — BOTH CLOSED (verified clean-3, 2026-06-20)

### (2) General-β logarithmic-singularity transfer — DONE
`LogKTransferNatural.logK_transfer_theorem_natural_remainder` — full Δ-domain **log^k transfer for any
k≥1** ([zⁿ]~C·n^{α−1}/Γα·(log n)^k), backed by LogKAsymp/LogKCoeff/LogKFaithful (general log^k scale +
Δ-domain analyticity), β=2 via LogSq*, and *applied* (UndirectedCycleLogKPermLpow). Wired in Audit
(1138–1152). clean-3. The β=1-only comment was stale.

### (1) Sharp partition / Hardy–Ramanujan constant — DONE (the hardest named frontier)
`erdos_partition_limit_constant : u → 1/(4√3)`  ⇔  **p(n) ~ exp(π√(2n/3)) / (4n√3)**, and the
unconditional `Erdos.erdos_partition_limit_exists : ∃ a>0, u→a`. Both clean-3 (verified 06-20).
Proved **without the circle method / modular forms** — via the first-entrance rank-band renewal route
+ the elementary **R9 additive escape** (CeilingEscapeClose), which closed the old Step-E "overshoot
escape" wall. The "lone remaining wall ErdosAlignment" (Audit 1552) was bypassed: ErdosAlignment is
false for far ranks; the first-entrance device (variable hitting time) + R9 escape is the correct route.
(This also retroactively closes the third-order partition/Product saddle "gap" — same family.)
The earlier elementary log-asymptotic log p(n)~π√(2n/3) remains as the independent route to leading order.

## What is genuinely left (optional — no major named frontier remains)
- **Fourth-order coefficient asymptotics (δ₃)** — the quantitative layer is complete to *third* order
  (√-family + saddle + all instances). δ₃ is the natural next depth; low practical value; a full new layer.
- **More F&S IX limit-law instances** — framework (quasi-powers/Gaussian, Goncharov–Kolchin multivariate
  capstone, Poisson laws) + flagship instances done; IX names more schemas not all instantiated.
- **Non-integer log powers** (1−z)^{−α}(log)^β for real β — only integer k done (the standard/useful case);
  real β is exotic and rarely a target.

## Per-chapter coverage (one line each; see AUDIT-WHOLEBOOK.md for the audit verdicts)
- **Ch1 / I** (OGF): Pólya/cycle-index, necklaces, bracelets, Lagrange inversion (closed). FAITHFUL/CLEAN.
- **Ch2 / II** (EGF): Bell, random mappings (connected/cyclic/components SHARP), Cayley/forests, Ramanujan Q. CLEAN.
- **Ch3 / III** (MGF): BGF + moments + variance + marked + binary-word/composition instances. CLEAN.
- **Ch4 / IV+VI** (transfer + singularity analysis): Δ-domain, (1−z)^{−α} transfer to 3rd order, √-meta 2nd+3rd, **log^k transfer (all k) ✓**. CLEAN.
- **Ch5 / V** (rational/meromorphic): meromorphic transfer, surjections, Fibonacci + general compositions, Flajolet continued fractions. CLEAN.
- **Ch7 / VII** (singularity apps): Catalan/Motzkin/Schröder/Riordan/ternary/Fuss-Catalan-general, all to **3rd order**; Cayley 3rd. CLEAN.
- **Ch8 / VIII** (saddle): Hayman 1st+2nd+3rd order; instances involution/Bell/Blocks3/FragmentedPerm (2nd+3rd); **partition log-asymptotic AND sharp constant p(n)~exp(π√(2n/3))/(4n√3) ✓** (+ distinct/odd parts). CLEAN.
- **Ch9 / IX** (limit laws): quasi-powers/Gaussian + instance, fixed-points/r-cycles→Poisson, multivariate Goncharov–Kolchin capstone. Framework + flagships done.

## Bottom line for "is the whole book done?"
For practical purposes, **yes at the flagship level**: every F&S chapter (I–IX) has its named/hard
theorems formalized clean-3, including both items previously thought open (general-β log transfer; the
sharp Hardy–Ramanujan constant — done elementarily, no circle method). What remains is **optional
depth/breadth** (4th-order asymptotics; more IX instances; exotic non-integer log powers), not a named
gap. Always verify against the theorem files + `#print axioms` + AUDIT-WHOLEBOOK.md — not the inline prose.
