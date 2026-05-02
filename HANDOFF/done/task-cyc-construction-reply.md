Implemented `AnalyticCombinatorics/PartA/Ch1/Cycle.lean`.

What is included:
- `cycClass`: a direct-count realization of a CYC construction as a `CombinatorialClass`.
- `cycAtomCount n = if n = 0 then 0 else (n - 1)!`.
- `cycAtomClass := cycClass cycAtomCount`.
- `cycClass_count`: the direct-count class has the prescribed count sequence.
- `cycAtom_ogf_coeff`: positive-size Atom cycles have count `(n - 1)!`.
- `cycAtom_egf_coeff`: the EGF coefficient is `1 / n`, matching the coefficient sequence of `-log(1 - z)`.
- `cycAtomCount_eq_labelCycCount`: agreement with the existing `labelCycCount Atom`.
- Sanity checks for sizes 1 through 5, both for `cycAtomCount` and `cycAtomClass.count`.

Verification:
- `lake build AnalyticCombinatorics.PartA.Ch1.Cycle`
- `rg "sorry|axiom|admit" AnalyticCombinatorics/PartA/Ch1/Cycle.lean` returned no matches.

Note:
- I did not construct quotient rotation orbits for general `CYC(B)`; this file follows the requested Atom-focused direct-count route.
