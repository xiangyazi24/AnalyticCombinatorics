# DOCTRINE — Whole-book F&S formalization (automode)

## Main goal (one sentence)

Complete the Lean 4 formalization of Flajolet & Sedgewick *Analytic Combinatorics*,
every headline theorem FAITHFUL and passing the formalization-playbook 3-group audit
(0 sorry / 0 axiom / 0 native_decide; `#print axioms` ∈ {propext, Classical.choice, Quot.sound};
statement fidelity to the book).

Approval: standing — `/goal 完成全书形式化, 以通过 audit 为准` + explicit `/automode`. No further
"确认开跑吗" gate (the goal directive overrides the handshake's wait-for-approval step).

## Current frontier (2026-06-14, overnight run, Xiang asleep)

ALL CHAPTERS PRESENT + ADVERSARIALLY AUDITED FAITHFUL:
- Ch1(I/OGF), Ch2(II/EGF), Ch3(III/BGF) — CLEAN.
- Ch4(IV complex + VI singularity analysis: transfer_theorem, DeltaDomain, standard scale
  [z^n](1-z)^{-α}~C n^{α-1}/Γ(α), LogSingularity) — fixed + audited.
- Ch5(V rational/meromorphic + Flajolet continued fractions) — CLEAN.
- Ch7(VII singularity apps; tree counts via Lagrange inversion, 钉死 this session) — clean-3, merged.
- Ch8(VIII saddle-point: HAdmissible 4 instances; + Partitions: HR limit erdos_partition_limit_exists) — FAITHFUL.
- Ch9(IX limit laws: quasi-powers, permutation cycle Gaussian) — fixed + audited.

Whole-book audit (this session): 6 independent Opus adversarial auditors (Ch1/2/3/5/8-SaddlePoint/
8-Partitions) + ChatGPT ac/ac2 faithfulness leg. Verdict: all FAITHFUL/CLEAN. Two disclosed SCOPE
NOTES remain (faithful-but-narrower than maximal FS), now the work:
  1. Ch2 CYC stated as ODE+uniqueness, not literal log closed form.
  2. Ch5 flajolet_cf is bounded-height + first-return-coded (no h→∞, no step-list bijection).

Build discipline: remote ONLY via `/tmp/acbuild.sh <Module>` on uisai2 (local lake BANNED, kernel
panic). **ONE build at a time** — concurrent acbuild rsyncs corrupt AC-clone (learned tonight).
codex unavailable (usage out); ChatGPT ac+ac2 online; Opus subagents for parallel grind.

## Avenues (ranked)

(a) **Close the audit loop** [fast; async parts — don't idle]. Retrieve ac (HR) ChatGPT answer +
    reconcile (Partitions already FAITHFUL); confirm `#print axioms erdos_partition_limit_exists`
    = clean-3; write `HANDOFF/AUDIT-WHOLEBOOK.md` (verdict table + 2 scope notes); commit.
    Terminal: summary committed + both confirmations in hand.

(b) **钉死 scope-note 1 — Ch2 CYC literal closed form** `CYC(C)(z) = -log(1-C(z))`.
    Current: `egf_lcyc_ode` (CYC' = C'·SEQ(C)) + `egf_lcyc_unique`. Mirror the `egf_set` exp
    derivation: Ch1 CycleOGF has `mlog f = ∑ f^{j+1}/(j+1) = -log(1-f)`. Show mlog(egf C) satisfies
    the same ODE + zero constant term → conclude by `egf_lcyc_unique`.
    Terminal: `egf_lcyc_closed` clean-3, OR written obstruction (which ODE→closed-form step fails).

(c) **钉死 scope-note 2 — Ch5 flajolet_cf unbounded height** (coeff level).
    Key: for fixed n, `Wcoeff h a b c n` stabilizes once h ≥ n. Prove stabilization lemma
    `n ≤ h → Wcoeff h a b c n = Wcoeff n a b c n`, define unbounded path-sum/J-fraction = height-n
    value, lift `flajolet_cf` to unbounded coeff statement.
    Terminal: `flajolet_cf_unbounded` (coeff-level) clean-3, OR obstruction. (step-list↔code
    bijection = SEPARATE bigger item; note, don't block.)

(d) **Stretch — HR exact constant a = 1/(4√3)** (full quantitative Hardy–Ramanujan).
    Current: ∃a>0 (honest fragment). Identifying a is genuine new analysis (renewal limit constant);
    use mass-rate K (MassRateApprox2, ties A=π²/6) + renewal-limit formula; dispatch ChatGPT for
    the constant-identification math. Terminal: a identified+proved, OR obstruction theorem.

## Fallbacks
- If (b)(c)(d) all blocked: deeper adversarial re-audit of the Ch4 singularity-analysis transfer
  core (FS Ch6 heart) + appendix math-background gaps vs Mathlib.
- A WALL → decompose into named sub-lemmas, grind each; never fake with axiom/sorry. Genuinely-absent
  Mathlib API → document exact missing shape, leave that one theorem unstated (not sorry'd), next brick.

## Terminal conditions recap
Success = clean-3 theorem committed (verified by my own rebuild + #print axioms). Failure = written
obstruction (a Lean `¬...` or precise file:line+tactic diagnosis), never "looks hard"/"to the limit".

## Workflow
Master (Opus) designs path + Mathlib survey + wiring + audit. ChatGPT ac/ac2 for math consult (with
paired waiter + truncation check). Opus subagents for parallel proof grind. ONE acbuild at a time;
per result: build → #print axioms → verdict → commit + push. git sync (no rsync).
