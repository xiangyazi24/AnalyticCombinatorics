# DOCTRINE — Whole-book F&S formalization (automode)

## Main goal (one sentence)

Complete the Lean 4 formalization of Flajolet & Sedgewick *Analytic Combinatorics*,
every headline theorem FAITHFUL and passing the formalization-playbook 3-group audit
(0 sorry / 0 axiom / 0 native_decide; `#print axioms` ∈ {propext, Classical.choice, Quot.sound};
statement fidelity to the book).

Approval: standing — `/goal 完成全书形式化, 以通过 audit 为准` + explicit `/automode`. No further
"确认开跑吗" gate (the goal directive overrides the handshake's wait-for-approval step).

## Current frontier (2026-06-03)

DONE/solid: Ch1(OGF/I), Ch2(EGF/II), Ch3(BGF/III), Ch4(complex+singularity/IV+VI incl Transfer VI.3),
Ch8(saddle/VIII: exp FAITHFUL, Hayman transfer CONDITIONAL-honest). 74 files, build green.
MISSING: F&S Ch V, Ch VII, Ch IX, Appendices A/B/C.

## Avenues (ranked; framework-first)

(a) **Ch V — Applications of Rational & Meromorphic.** Foundational brick: general meromorphic
    coefficient transfer (F&S IV.10) — analytic remainder =O(R^{-n}) via `norm_coeff_le_of_circleIntegral`,
    pole-subtraction decomposition, dominant simple-pole asymptotic. Then applications: surjections
    (EGF 1/(2-e^z), `egf_surjections` already proved → dominant pole at log 2), supercritical sequences,
    alignments. STATUS: meromorphic-transfer brick dispatched to codex.

(b) **Ch VII — Applications of Singularity Analysis.** Infra (Transfer VI.3) exists. Bricks: simple
    varieties of trees / Cayley tree asymptotics, tree-counting via singularity, supercritical-sequence
    schema, the √-singularity universality examples. Each is an application of the existing transfer.

(c) **Ch IX — Multivariate / Limit Laws.** Infra (Ch3 BGF: mean/variance) exists. Bricks: quasi-powers
    theorem (Hwang) → Gaussian limit law; CLT for sequence/set parameters from BGF mean+variance.

(d) **Ch8 deepening.** Wire exp as the first `HAdmissible` instance (CONDITIONAL → FAITHFUL for the
    general interface). Optionally Bell H-admissibility.

(e) **Appendices A/B/C.** Faithful statements of the named auxiliary results (many are Mathlib
    re-exports — must be genuine, not trivially-true re-skins).

## Fallbacks

- A foundational theorem that is a WALL → decompose into named sub-lemmas, grind each; never fake with
  axiom/sorry. Dispatch long proof chains to codex single-line (no effort cap in brief).
- If a brick blocks on a genuinely-absent Mathlib API, document the exact missing lemma/shape in the
  reply + RUN_LOG, leave that one theorem unstated (not sorry'd), move to next independent brick.

## Terminal condition per avenue

Every named F&S theorem in the chapter is either FAITHFUL-proved (audit-clean) or documented as
blocked on a specific missing piece. No "feels done" / "to the limit" exits.

## Workflow

Master (Opus) designs path + Mathlib survey + wiring + audit. Codex (gpt-5.5, uisai1) grinds proof
chains as `codex exec` nohup, reply → HANDOFF/outbox/*-reply.md. One file one writer; master wires
imports + Audit.lean + #print axioms + commit + push. git sync (no rsync). Per-brick: pull → lake env
lean → #print axioms → AUDIT_STATUS verdict → commit. Build green check before each Telegram milestone.
