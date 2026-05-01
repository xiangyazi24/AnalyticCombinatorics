# Task — Catalan / Stirling recurrence numerical sanity

## File 1: `AnalyticCombinatorics/Examples/CatalanFamily.lean` (append)

Add Catalan recurrence numerical sanity for small `n`, using the just-landed `catalan_recurrence`:

- `n = 0`: `C_1 = C_0 * C_0 = 1`
- `n = 1`: `C_2 = C_0*C_1 + C_1*C_0 = 1 + 1 = 2`
- `n = 2`: `C_3 = C_0*C_2 + C_1*C_1 + C_2*C_0 = 2 + 1 + 2 = 5`
- `n = 3`: `C_4 = 5 + 2 + 2 + 5 = 14`
- `n = 4`: `C_5 = 14 + 5 + 4 + 5 + 14 = 42`

5 examples. Use `catalan_recurrence n` then `decide` / `native_decide`.

## File 2: `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

Add Stirling 2nd recurrence numerical sanity:

- `S(2, 1) = 1*S(1,1) + S(1,0) = 1 + 0 = 1`
- `S(3, 2) = 2*S(2,2) + S(2,1) = 2 + 1 = 3`
- `S(4, 2) = 2*S(3,2) + S(3,1) = 6 + 1 = 7`
- `S(5, 3) = 3*S(4,3) + S(4,2) = 18 + 7 = 25`

4 examples. Use `stirlingSecond_succ` then `decide`.

Also add Stirling 1st kind numerical sanity:

- `c(2, 1) = 1*c(1,1) + c(1,0) = 1`
- `c(3, 2) = 2*c(2,2) + c(2,1) = 2 + 1 = 3`
- `c(4, 2) = 3*c(3,2) + c(3,1) = 9 + 2 = 11`

3 examples. Use `stirlingFirst_succ`.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-cat-rec-sanity-reply.md.
- Both files in this single dispatch.
