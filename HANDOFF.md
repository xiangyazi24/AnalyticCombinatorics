# HANDOFF — AnalyticCombinatorics 协作模式

**Repo:** `~/repos/AnalyticCombinatorics` (github.com/xiangyazi24/AnalyticCombinatorics)
**Project:** Formalize Flajolet & Sedgewick *Analytic Combinatorics* in Lean 4.
**Driver:** Zinan (Claude Opus 4.7, dm window).
**Partner:** Sonnet (Claude Sonnet 4.6, tmux window `zinan:ac`).

## Roles

- **Zinan (driver / architect):** chooses targets, audits proofs, fixes scaffold, commits.
- **Sonnet (proof writer):** picks up task files in `HANDOFF/inbox/`, edits `.lean` files, runs `lake build`, reports back.

## Communication channel — file-based

```
HANDOFF/
  inbox/    # tasks Zinan → Sonnet         (task-N-<slug>.md)
  outbox/   # replies Sonnet → Zinan       (task-N-<slug>-reply.md)
  done/     # archived threads (after I review and accept)
  locks/    # write <relpath>.lock before editing a file you don't own
```

A task file is self-contained:
- exact lemma statement (with file path + line number)
- what's already proved nearby (so partner doesn't waste context re-discovering)
- recipe hints if I have them
- a concrete acceptance check: "after edit, `lake build` passes with one fewer `sorry`"

A reply file states one of:
- **done** — proof landed, build green, here's the diff summary
- **blocker** — couldn't close it, here's exactly where it broke (don't axiom-escape, don't replace `sorry` with `True`)
- **handover** — flailed ≥ 2 attempts, returning to driver

## Tmux ping convention

To ping the partner that a new task is in `inbox/`:

```
tmux send-keys -t zinan:ac 'Zinan: new task in HANDOFF/inbox/task-1-disjSum-ogf.md' Enter
```

**Every send-keys MUST end with the literal `Enter` keyword.** Without it the text only types into the prompt buffer; the partner never receives it.

## Signature convention

Every tmux line between Zinan and Sonnet starts with the sender's name + colon:

- `Zinan: ...` — from me
- `Sonnet: ...` — from partner

Xiang's messages on this pane are unsigned and override the protocol.

## Hard rules for partner (Sonnet)

1. **Never** replace `sorry` with `axiom`, `True`, `trivial` on a non-trivial goal, or any other escape hatch. If you can't prove it, file a blocker.
2. **Never** edit `CombinatorialClass.lean` core definitions (`structure CombinatorialClass`, `level`, `count`, `ogf`, `coeff_ogf`) without filing a blocker first — those are scaffold-defining.
3. **Two real attempts → blocker.** Don't loop on a structurally-broken statement.
4. `lake build` must be green at every commit boundary. Sorry warnings OK; errors are not.
5. If you need to edit a file the other side might also be editing, write `HANDOFF/locks/<relpath>.lock` first, remove on release.

## Build command

```bash
cd ~/repos/AnalyticCombinatorics && lake build
```

Expected baseline (commit 5008de8): 2695 jobs, 0 errors, sorry warnings only.

## Current state (2026-04-29)

9 sorry sites:
- `PartA/Ch1/CombinatorialClass.lean:110` — `disjSum_ogf` ← **task 1**
- `PartA/Ch1/CombinatorialClass.lean:129` — `cartProd_ogf` ← **task 2**
- `PartA/Ch1/Sequences.lean:20`, `:30` — `seqClass.finite_level`, `seqClass_ogf_eq`
- `Examples/BinaryTrees.lean:36`, `:44` — `BinTree.asClass.finite_level`, `ogf_functional_equation`
- `Complex/TransferTheorems.lean:34`, `:47` — old scaffold `dominantSingularity`, transfer
- `SymbolicMethod/CombinatorialClass.lean:43` — duplicate scaffold (will be removed)

## Status board

See `HANDOFF/STATUS.md` for the live task list.
