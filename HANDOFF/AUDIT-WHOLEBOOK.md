# Whole-book adversarial audit — Flajolet & Sedgewick formalization

Date: 2026-06-14. Protocol: formalization-playbook §3.1 (17-point, 3-group) +
§3.3 (independent adversarial audit). Method: independent read-only auditors
(default stance "it has holes, break it"), orchestrator re-checks each finding
against source + classical math (does NOT self-audit). codex unavailable;
independent leg = 6 Opus auditors; faithfulness cross-check = ChatGPT ac/ac2
(repo-connected). Group-A `#print axioms` verified centrally by rebuild.

## Verdict: whole book FAITHFUL / CLEAN

| Chapter (FS) | Repo | Auditor | Verdict | Scope note |
|---|---|---|---|---|
| I — OGF symbolic | Ch1 | Opus | FAITHFUL (CLEAN) | — |
| II — EGF labelled | Ch2 | Opus | FAITHFUL (CLEAN) | CYC stated as ODE+uniqueness, not literal log closed form |
| III — BGF parameters | Ch3 | Opus | FAITHFUL (CLEAN) | — |
| IV + VI — complex + singularity analysis | Ch4 | (earlier §3.3) | FAITHFUL (fixed: LogSingularity) | transfer_theorem genuine (Δ-domain + O-transfer + standard scale) |
| V — rational/meromorphic + continued fractions | Ch5 | Opus + ChatGPT ac2 | FAITHFUL (CLEAN) | flajolet_cf bounded-height + first-return-coded (no h→∞, no step-list↔code bijection) |
| VII — singularity apps (tree counts) | Ch7 | (this session, 钉死) | FAITHFUL, clean-3 | tree counts via Lagrange inversion (no Prüfer/Rothe-Hagen) |
| VIII — saddle point | Ch8/SaddlePoint | Opus | FAITHFUL (CLEAN) | HAdmissible satisfiable (4 instances), cross-checked vs Mathlib Stirling |
| VIII — partitions (Hardy–Ramanujan) | Ch8/Partitions | Opus + ChatGPT ac | FAITHFUL | honest HR *fragment*: rate C=π√(2/3) + n^{-1} order + positive constant, NOT a=1/(4√3) (by design) |
| IX — limit laws | Ch9 | (earlier §3.3) | FAITHFUL (fixed: cycle Gaussian) | quasi-powers + permutation cycle CLT |

No vacuity, no assumption-smuggling, no too-strong/weakened predicates, no
fragment/trivial impostors, no hidden sorry/admit/axiom/native_decide on any
load-bearing path. The 3 findings from the earlier §3.3 round (Ch4 LogSingularity,
Ch9 cycle Gaussian, Ch7 tree counts) were all fixed to full strength this campaign.

## Two scope notes (faithful-but-narrower than maximal FS; docstring-disclosed)

These are NOT defects — each is honest within its stated scope. They are the
maximal-fidelity extension targets (genuine additional math):

1. **Ch2 CYC closed form.** `egf_lcyc_ode` + `egf_lcyc_unique` characterize the
   labelled-cycle EGF by `CYC(C)' = C'·SEQ(C)` and zero constant term; the literal
   `CYC(C) = log(1/(1-C))` was not stated (Mathlib has no formal-series log).
   → ADDRESSED 2026-06-14: `Ch2/EGF/LabelledCycExp.lean` proves the exponentiated
   closed form `exp(CYC(C)) = SEQ(C)` (= CYC = log(1/(1-C))). [verify build]

2. **Ch5 flajolet_cf height bound.** `flajolet_cf` proves the bounded-height,
   first-return-coded J-fraction = path sum identity. No h→∞ statement; the
   step-list↔first-return-code bijection is separate.
   → PARTLY ADDRESSED 2026-06-14: `Ch5/ContinuedFractions/FlajoletUnbounded.lean`
   proves height-independence `Wcoeff h = Wcoeff n` for h≥n (the bound is
   immaterial per coefficient), i.e. the bounded J-fractions agree with the full
   unbounded continued fraction in every coefficient. [verify build]
   (The step-list↔code bijection remains a separate, larger item.)

## Deferred: full quantitative HR (Ch8 partitions)

`erdos_partition_limit_exists` proves ∃a>0 (honest fragment). Identifying
a = 1/(4√3) is full quantitative Hardy–Ramanujan — under investigation
(extractable from renewal/mass-rate machinery, or needs independent
saddle-point/circle-method input?). See DOCTRINE avenue (d).
