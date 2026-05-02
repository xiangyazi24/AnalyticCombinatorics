# Task: Integer Partitions OGF Theory — Part A Ch I

## Goal

Create file `AnalyticCombinatorics/PartA/Ch1/IntPartTheory.lean` connecting integer partitions to the MSET/OGF framework.

## What to formalize

Integer partitions = MSET(positive integers). The OGF is the Euler product:
- `P(z) = ∏_{k≥1} 1/(1 - z^k)`

Key identities:
- Euler's pentagonal number theorem (partial): `∏(1-z^k) = Σ (-1)^n z^{n(3n-1)/2}`
- Euler's odd-distinct identity: number of partitions into odd parts = number into distinct parts

### Required:

1. **Connect `msetClass Atom` to partitions:**
   The file Multiset.lean already shows MSET of the "all positive sizes" class counts partitions. Add:
   ```lean
   theorem intPartition_ogf_coeff (n : ℕ) :
       intPartClass.count n = Nat.Partition.count n
   ```
   (where `intPartClass` is the MSET-of-all-sizes class from Multiset.lean, and `Nat.Partition.count` is from Mathlib)

2. **Euler's odd-distinct theorem (finite verification):**
   Define:
   - `oddPartCount n` = number of partitions of n into odd parts
   - `distinctPartCount n` = number of partitions of n into distinct parts
   
   Prove equality for n = 0..10 via native_decide.

3. **Partition function recursion:**
   ```lean
   theorem partition_count_recursion (n : ℕ) (hn : 0 < n) :
       Nat.Partition.count n = ∑ k ∈ Finset.range n, (if (n - k) % ... then ... else ...)
   ```
   Actually simpler: verify the recursion `p(n) = Σ_{k=1}^{n} σ(k) * p(n-k) / n` ... this is complex.

   Instead, prove the **Euler recurrence** using pentagonal numbers:
   ```lean
   def pentagonal (k : ℤ) : ℕ := (k * (3*k - 1) / 2).toNat
   ```
   and state that p(n) = Σ (-1)^{k+1} [p(n - ω(k)) + p(n - ω(-k))] for the first few terms.

4. **Sanity (partition numbers):**
   - p(0) = 1, p(1) = 1, p(2) = 2, p(3) = 3, p(4) = 5, p(5) = 7, p(6) = 11, p(7) = 15, p(8) = 22, p(9) = 30, p(10) = 42

## Imports

```lean
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Multiset
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch1.IntPartTheory` must pass
- Focus on sanity checks and the odd=distinct verification. Skip heavy infinite product proofs.
- If `Nat.Partition.count` is not directly available in this Mathlib version, define locally.

## Output

Write the file and report.
