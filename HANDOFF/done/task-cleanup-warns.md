# Task — silence linter warnings (cleanup)

**File:** any file with linter warnings.

**Goal:** Run `lake build`, look at warnings, silence trivial style warnings (`show` linter, etc.) by adding `set_option linter.style.X false` or by structural rewrites.

If a warning needs a substantive code change, leave it (file blocker). Focus on quick wins.

## Hard constraints

- Build green
- No new sorrys
- Don't change semantics, just silence cosmetic warnings
- Reply at HANDOFF/outbox/task-cleanup-warns-reply.md
