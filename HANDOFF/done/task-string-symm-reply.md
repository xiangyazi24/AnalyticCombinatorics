Implemented option B.

I added `stringClass_jointCount_stringNumTrue`:

```lean
theorem stringClass_jointCount_stringNumTrue (n k : ℕ) :
    stringClass.jointCount stringNumTrue n k = Nat.choose n k
```

This was clean because `stringNumTrue` is definitionally `numOnes`, and
`stringClass_jointCount_numOnes` was already proved in the file for all `n k`
(including the out-of-range zero case through `Nat.choose`).

I also added option A as a corollary:

```lean
theorem stringClass_jointCount_stringNumTrue_symm {n k : ℕ} (hk : k ≤ n) :
    stringClass.jointCount stringNumTrue n k =
      stringClass.jointCount stringNumTrue n (n - k)
```

Verification:

```text
lake env lean AnalyticCombinatorics/Examples/Strings.lean
lake build
```

Both passed.
