# Task: Generating Function Operations (Ch I/III)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/GFOperations.lean`.

## What to formalize

Core generating function operations from the symbolic method.

1. **Hadamard product (coefficient-wise):**
   ```lean
   def hadamardProduct (f g : ℕ → ℕ) : ℕ → ℕ := fun n => f n * g n
   ```
   
   Verify: hadamardProduct (fun n => 2^n) (fun n => n + 1) gives
   n=0: 1, n=1: 4, n=2: 12, n=3: 32, n=4: 80

2. **Sequence construction OGF:**
   If B has OGF B(z), then SEQ(B) has OGF 1/(1-B(z)).
   Coefficient extraction: if b_0 = 0, then [z^n] 1/(1-B(z)) = sum over compositions.
   
   For b_n = 1 (n≥1): SEQ coefficients are 2^{n-1} for n≥1.
   Verify: seqCount n = if n = 0 then 1 else 2^(n-1) for n=0..8.

3. **Multiset construction:**
   MSET(B) has OGF = ∏_{k≥1} 1/(1-z^k)^{b_k} where b_k = [z^k]B(z).
   
   For b_k = 1 for all k≥1 (B = z/(1-z)):
   MSET counts = integer partition p(n).
   Verify: msetPartitionCount matches p(n) for n=0..10.
   
   ```lean
   def msetPartitionCount : ℕ → ℕ
     | 0 => 1
     | n + 1 => (∑ k ∈ Finset.range (n + 1),
                   (∑ d ∈ Nat.divisors (k + 1), d) * msetPartitionCount (n - k)) / (n + 1)
   ```
   This uses the Euler recurrence: (n+1)*p(n+1) = Σ_{k=1}^{n+1} σ(k) * p(n+1-k).

4. **Powerset construction:**
   PSET(B) = ∏_{k≥1} (1+z^k)^{b_k}.
   For b_k = 1: counts distinct-part partitions q(n).
   q(0)=1, q(1)=1, q(2)=1, q(3)=2, q(4)=2, q(5)=3, q(6)=4, q(7)=5, q(8)=6
   
   Verify these values.

5. **Cycle construction:**
   CYC(B) has OGF = Σ_{k≥1} φ(k)/k * log(1/(1-B(z^k))).
   For binary alphabet (b_1 = 2): CYC counts binary necklaces.
   Already covered in Necklaces.lean. Just cross-reference.

## Imports

```lean
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.GFOperations`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace GFOperations`** and close with `end GFOperations`
- If the Euler partition recurrence is hard to make terminating, use a simpler recursion or explicit table

## Output

Write file, verify build, report.
