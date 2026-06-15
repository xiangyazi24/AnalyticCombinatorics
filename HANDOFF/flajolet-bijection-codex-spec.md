# Codex task: finish the Flajolet step-list bijection (Ch5)

## Goal
Make `flajolet_cf` a theorem about GENUINE lattice paths (step lists), not the first-return-coded
`MotzkinPath` type. You OWN the file `AnalyticCombinatorics/Ch5/ContinuedFractions/FlajoletPathBijection.lean`
(no one else edits it). Final deliverable: that file builds clean-3 axioms
`{propext, Classical.choice, Quot.sound}`, 0 `sorry`/`admit`/`native_decide`, with the capstone theorem

```lean
theorem coeff_JFraction_eq_stepPathSum {R : Type*} [CommRing R]
    (h n : ℕ) (a b c : ℕ → R) :
    PowerSeries.coeff (R := R) n (JFraction h a b c)
      = ∑ p ∈ closedMotzkinFinset h n, stepWeight a b c 0 p
```
(or, equivalently, an `Equiv (MotzkinPath h n) {p : List Step // ClosedMotzkin h n p}` that is
weight-preserving, then transported). Pick whichever is cleaner; the `Finset`-sum form is the honest
combinatorial statement. Then connect to the banked `coeff_JFraction_eq_pathSum`
(in `FlajoletPathSum.lean`: `coeff n (JFraction h a b c) = WpathSum h a b c n`,
`WpathSum h a b c n = ∑ p : MotzkinPath h n, pathWeight a b c h n p`).

## Already banked in the file (DO NOT change; build on them)
- `endLevel s p` (level after running step list), `endLevel_append`.
- `Walk h s p` inductive (floor-0/ceiling-h validity), `ClosedMotzkin h n p := Walk h 0 p ∧ endLevel 0 p = 0 ∧ p.length = n`.
- `stepWeight a b c s p` (genuine step-product weight; down from level s weighs `b (s-1)`).
- `stepWeight_append`, `stepWeight_shift` (valid-walk version: `Walk H s p → stepWeight a b c (s+1) p = stepWeight (shift a) (shift b) (shift c) s p`).
- `toSteps h n p` (code → step list; arch ↦ `up :: inner ++ down :: rest`).

## Lemmas to prove (structural direction — mechanical)
1. `endLevel_toSteps : endLevel s (toSteps h n p) = s` (balanced). Use `toSteps.induct`. 3 of 5 cases
   already pass with `simp [toSteps, endLevel_cons, Step.nextLevel, ih]`; cases 2/4/5 need the cast
   handled — see TECHNIQUE below.
2. `toSteps_length : (toSteps h n p).length = n`.
3. `Walk_shift : Walk h s p → Walk (h+1) (s+1) p` (level relabel; induction on Walk).
4. `toSteps_walk : Walk h 0 (toSteps h n p)` (arch interior uses Walk_shift to lift inner from base 0 to base 1).
5. `toSteps_closed : ClosedMotzkin h n (toSteps h n p)` (combine 1,2,4).
6. `stepWeight_toSteps : stepWeight a b c 0 (toSteps h n p) = pathWeight a b c h n p`.
   Arch case: `stepWeight_append` + `endLevel_toSteps` (inner returns to its base, so `endLevel 1 inner = 1`)
   + `stepWeight_shift` (s=0, on the valid inner walk) + the two IHs. The algebra:
   `stepWeight 0 (up::A++down::B) = a0 * stepWeight 1 A * b0 * stepWeight 0 B`
   `= a0*b0* pathWeight(shift) h i inner * pathWeight (h+1)(n-i) rest`.

## The HARD lemma (first-return parse — surjectivity / invFun)
7. `toSteps_surj : ClosedMotzkin h n p → ∃ q : MotzkinPath h n, toSteps h n q = p`,
   and `toSteps_inj` (injective). Together ⟹ `toSteps` is a bijection MotzkinPath h n ≃ {closed paths}.
   PROOF by strong induction on `n` (length):
   - n=0: p=[], only PUnit code.
   - p = level :: q with first step a level at level 0: q is ClosedMotzkin h (n-1); recurse → inl code
     (for h=0) / inl-of-arch (for h+1: the `Sum.inl` branch).
   - p = up :: q: the walk goes to level 1; let the FIRST RETURN to level 0 be at index k (the first
     `down` that lands at 0). Split p = up :: inner ++ down :: rest where `inner` stays ≥1 throughout
     (length i = k-1), `rest` is ClosedMotzkin h (n-2-i). `inner` shifted DOWN by 1 is ClosedMotzkin
     (h-1) i (use the inverse of Walk_shift: a walk staying ≥1 from level 1 ↔ Walk (h-1) 0 of the same
     list). Recurse on inner (length i < n) and rest (length < n) → inr code with that `i`.
   - p can't start with `down` (Walk has no down-from-0 constructor).
   The first-return index existence: since the walk starts at 1 (after up) and ends at 0, and steps
   change level by ≤1, there is a first prefix reaching 0; that prefix ends in a `down` from 1.
   You may build a helper `firstReturn : List Step → ℕ` (least k with endLevel 1 (take k q) = 0) and the
   split lemmas. This is the genuine combinatorial core — grind it patiently.

## TECHNIQUE for the cast (PROVEN, mirror it)
`MotzkinPath` is a recursive `def` (not inductive); `toSteps`/`pathWeight` match on
`(by simpa [MotzkinPath] using p : <unfolded ⊕/Σ type>)`. The banked proof
`WpathSum_eq_Wcoeff` (FlajoletPathSum.lean lines 31-146) shows the technique:
- `Wcoeff.induct` (or `toSteps.induct`) for the recursion;
- the auto-generated `MotzkinPath.eq_2`, `MotzkinPath.eq_4` (the type-equation lemmas) with `.mp`;
- `fintype_sum_eq_mp` to transport `Finset.univ` sums across the `.mp` cast;
- `change` to expose the reduced match, then `Fintype.sum_sum_type` / `Fintype.sum_sigma` to split
  the `⊕`/`Σ` sum into the inl (level) + inr (arch) pieces.
For non-sum lemmas (endLevel/length/walk/weight on a single code), after `toSteps.induct` the goal's
`toSteps h n p` may need `rw [toSteps]` then resolving the cast `(by simpa [MotzkinPath] using p)`
against the IH subject — they are defeq; `exact ih s` / `convert ih s using 2` / `simp only [toSteps]`
should close it. If `rw [toSteps]` fails to reduce the match in the inl/inr cases, use the generated
equation lemmas `toSteps.eq_4`/`toSteps.eq_5` or `show` the reduced form.

## Verify (MANDATORY each iteration)
- Build ONLY this module, remotely (local lake is BANNED):
  `bash /tmp/acbuild.sh AnalyticCombinatorics.Ch5.ContinuedFractions.FlajoletPathBijection`
  (one at a time — concurrent rsync corrupts).
- When green + 0 sorry, audit: create /tmp a `#print axioms coeff_JFraction_eq_stepPathSum` checker
  via `ssh uisai2 "... lake env lean <file>"` (mirror the pattern already used in the session), must be
  exactly `{propext, Classical.choice, Quot.sound}`.
- Do NOT use `native_decide`, `axiom`, or leave any `sorry`. Report exactly what blocks if stuck; no faking.
- Commit when fully green: `git add` the ONE file + commit (msg ending
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`). Do not push.
