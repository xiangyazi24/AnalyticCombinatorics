# Task — stringClass bivariate refinement (number of 1s)

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

The file already builds `stringClass = seqClass boolClass` with `count n = 2^n`. Add a parameter `numTrue` that counts how many `true` bits appear, and derive bivariate sanity / structural lemmas.

## What to add

1. A `Parameter` `stringNumTrue : Parameter stringClass` that returns the number of `true`s in the underlying list of bools. (See `Examples/Compositions.lean`'s `numParts` for the existing bivariate `Parameter` pattern.)

2. Sanity examples for the joint count `stringClass.jointCount stringNumTrue n k` matching binomial coefficients:

   ```lean
   example : stringClass.jointCount stringNumTrue 3 0 = 1 := by ...  -- (3 choose 0)
   example : stringClass.jointCount stringNumTrue 3 1 = 3 := by ...
   example : stringClass.jointCount stringNumTrue 3 2 = 3 := by ...
   example : stringClass.jointCount stringNumTrue 3 3 = 1 := by ...
   example : stringClass.jointCount stringNumTrue 4 2 = 6 := by ...
   ```

3. The sum identity:

   ```lean
   example : ∑ k ∈ ..., stringClass.jointCount stringNumTrue 4 k = 16 := ...
   ```

   (Or use `jointCount_sum_eq_count` from `Ch3/Parameters.lean` to derive it cleanly.)

## Hard constraints

- Build green.
- No new sorrys.
- Don't refactor existing string defs.
- If extracting "number of trues from a `seqClass` element" is awkward (might need `Quot.lift` / unfolding `seqClass` Obj), document the impedance and **just** ship sanity (drop step 3) rather than force.
- Reply at HANDOFF/outbox/task-string-bivariate-reply.md.
