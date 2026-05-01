# Dispatch stats log

Tracked per-task for analysis: task name, dispatch mode, duration, tokens, result.

| date_time | task | mode | duration | tokens | result | notes |
|-----------|------|------|----------|--------|--------|-------|
| 2026-04-30 20:12 | task-dispatch-test-codex | exec(codex) | ~3min | 20851 | done | pipeline validation; one-line proof |

Modes:
- `exec(codex)` — handoff-dispatch.sh codex (one-shot codex exec --full-auto)
- `exec(sonnet)` — handoff-dispatch.sh sonnet (one-shot claude -p)
- `tmux(codex)` — tmux send-keys to dm-codex (long session)
- `tmux(sonnet)` — tmux send-keys to dm-sonnet (long session)
- `zinan` — Opus did it directly (trivial; no dispatch)
