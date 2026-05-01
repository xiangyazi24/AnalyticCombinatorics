Done.

- Added `numOnes : Parameter stringClass`.
- Proved `stringClass_jointCount_numOnes (n k) :
  stringClass.jointCount numOnes n k = n.choose k`.
- Added the requested small sanity examples.
- No new `sorry`/`admit`/`axiom` in `Strings.lean`.
- Verification: `lake env lean AnalyticCombinatorics/Examples/Strings.lean` and `lake build` both pass.

Note: `lake build` still reports pre-existing style warnings in earlier files and earlier lines of
`Strings.lean`; the new section builds without introducing proof blockers.
