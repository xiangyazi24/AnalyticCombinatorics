# AnalyticCombinatorics — coverage map & genuine open frontiers
_Read-only comb-through of Audit.lean (1754 lines, 576 `#print axioms`, 417 .lean files), 2026-06-20._

## Headline
The formalization is **highly complete** — it carries flagship/named theorems across **all nine F&S
chapters (I–IX)**, each clean-3 (axioms ⊆ {propext, Classical.choice, Quot.sound}, 0 sorry/admit/native_decide).
It is *selective* (flagship theorems), not page-by-page exhaustive — F&S is ~800pp.

**Crucial finding:** the ~47 `PARTIAL`/`frontier`/`conditional` markers are **mostly historical** — written
when a result was first banked partial, then **closed by later work**. Verified examples of markers that are
NOT gaps anymore:
- saddle "instances not yet supplied" (512) → closed: expHAdmissible + involution/Bell/Blocks3/FragmentedPerm instances.
- quasi-powers "no instance yet" (556) → closed: binary-word Gaussian instance (564).
- r-cycles "left conditional" (584) → "COMPLETED to UNCONDITIONAL" (596).
- fixed-points "blocked on pmf⟹weak bridge" (571) → closed by the reusable bridge (575).
- Ramanujan Q PARTIAL (642) → FULL unconditional (649); generalized Cayley PARTIAL (655) → COMPLETE (663).
- Lagrange "documented frontier" (706) → "LAGRANGE INVERSION CLOSED" (714).
- components PARTIAL sandwich (693) → SHARP ~½log n unconditional (699).
- partition Milestone B PARTIAL (788) → COMPLETE (802); Tauberian PARTIAL (808) → COMPLETE (822).
- general compositions PARTIAL (1241) → COMPLETE (1249); Goncharov >2 (605) → multivariate capstone (632).

## GENUINE open frontiers (what is actually NOT done)

### 1. ★ Sharp partition asymptotic — the one major contested frontier
p(n) ~ e^{π√(2n/3)} / (4n√3). The **log-asymptotic log p(n) ~ π√(2n/3) IS done** (elementary, end-to-end:
GF bound → Euler product → Laplace π²/6 → reusable log-Tauberian → monotone transfer; 829–836), incl.
distinct-parts and odd-parts. **Open = the sharp polynomial prefactor** (the "4n√3" and the e^{...} constant).
Two documented routes:
  - (a) circle method / Rademacher / Dedekind-η modularity — Mathlib lacks all of this (major ANT infra).
  - (b) the **"HR mass-rate campaign"** (Audit 1460–1556, bricks 56–76, IN PROGRESS): a renewal/coupling
    route (super/sub-harmonic barriers, windowed coupling, scalar recursion). Reduced to **one named
    analytic wall: `ErdosAlignment`** (comparable-rank overlap + descent coupling). If that wall falls, u→a>0
    and the sharp constant follows without modularity.
This is also the obstruction to the *third-order* partition/Product saddle instance (the documented gap from
the third-order run).

### 2. General logarithmic-singularity transfer  [F&S VI.2]
[z^n](1−z)^{−α} log^β(1/(1−z)). Only **β=1 leading order** is done (1255–1259, α=2 ~ n log n instance).
General β (and full Δ-domain log-transfer to all orders) is honestly reported open. Tractable-looking:
extend the existing Δ-domain machinery; no external infra needed. **Best "tractable next" item.**

### 3. Depth: fourth-order coefficient asymptotics (δ₃)
The quantitative layer now goes to **third order** (√-family + saddle + the new instances). Fourth order
(δ₃ via the next Wick grade + 4th-order structures/instances) is the natural depth extension. Low practical
value (4th-order coefficient asymptotics are rarely used); a full new layer. Not a named book gap.

### 4. Breadth, F&S IX limit laws
The limit-law *framework* (quasi-powers/Gaussian, Poisson via Goncharov, multivariate Goncharov–Kolchin
capstone) + key instances are done. F&S IX names many more schemas (singularity-analysis-based limit laws,
the various combinatorial schemas) that are not all instantiated — framework is non-vacuous but not exhausted.

## Per-chapter coverage (one line each)
- **Ch1 / F&S I** (OGF): Pólya/cycle-index, necklaces, bracelets (dihedral PET), Lagrange inversion (CLOSED). Solid.
- **Ch2 / F&S II** (EGF): Bell partitions, random mappings (connected/cyclic/components all SHARP), Cayley/forests, Ramanujan Q (full). Solid.
- **Ch3 / F&S III** (MGF/parameters): BGF defs + moments + variance + marked seq/set + binary-word/composition moment instances. Core done; deeper multivariate/parameter limit theory lighter.
- **Ch4 / F&S IV+VI** (transfer/singularity analysis): Δ-domain, general (1−z)^{−α} transfer (1st/2nd/3rd order), √-meta (2nd/3rd). **Open: general-β log transfer (#2).**
- **Ch5 / F&S V** (rational/meromorphic): meromorphic transfer, surjections, Fibonacci + general compositions (COMPLETE), Flajolet continued fractions. Solid.
- **Ch7 / F&S VII** (singularity-analysis apps): Catalan/Motzkin/Schröder/Riordan/ternary/Fuss-Catalan-general, all to **third order**; Cayley tree to 3rd. Solid.
- **Ch8 / F&S VIII** (saddle point): Hayman H-admissible (1st+2nd+3rd order abstract), instances involution/Bell/Blocks3/FragmentedPerm (2nd+3rd), partition log-asymptotic + Erdős/odd. **Open: sharp partition prefactor (#1).**
- **Ch9 / F&S IX** (limit laws): quasi-powers/Gaussian + binary-word instance, fixed-points/r-cycles → Poisson, multivariate Goncharov–Kolchin capstone. Framework + flagships done; **breadth (#4).**

## Bottom line for "is the whole book done?"
No — but it is far more complete than the marker count suggests. Every chapter has its flagship theorems
clean-3. The genuine open list is short: **(1) the sharp partition constant** (the one hard named frontier,
actively attacked via the renewal route, one wall left), **(2) general-β log-singularity transfer** (tractable),
plus optional **(3) fourth-order depth** and **(4) more IX instances**. Items needing external Mathlib infra
(circle method / modularity) are isolated to (1a).
