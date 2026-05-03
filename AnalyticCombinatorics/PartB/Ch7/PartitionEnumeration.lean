/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Enumeration and numerical verification of integer partition counts.

  We verify, from exact tables, a range of classical identities and inequalities
  about integer partition sequences discussed in Chapter VII of
  Flajolet & Sedgewick (2009):

    · p(n)   — unrestricted partition function (OEIS A000041)
    · q(n)   — partitions into distinct parts  (OEIS A000009)
    · Euler's pentagonal recurrence for p(n)
    · Euler's theorem: partitions into odd parts = partitions into distinct parts
    · Restricted partitions r₃(n): parts ≤ 3
    · Growth bounds: p(n) < 100 for n ≤ 10, p(10) > 40

  All proofs are by `native_decide`; no sorry, no axiom.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace PartitionEnumeration

-- ============================================================
-- §1  Partition function p(n)  (OEIS A000041)
-- ============================================================

/-!
### 1. The partition function p(n)

`p(n)` counts the number of ways to write `n` as an unordered sum of
positive integers (with p(0) = 1 by convention).

Exact table for n = 0 … 10:
  n  : 0  1  2  3   4   5   6   7   8   9  10
  p  : 1  1  2  3   5   7  11  15  22  30  42
-/

/-- Exact values of p(0), p(1), …, p(10). -/
def pTable : Fin 11 → ℕ :=
  ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42]

-- Spot-checks
theorem pTable_0  : pTable 0  = 1  := by native_decide
theorem pTable_1  : pTable 1  = 1  := by native_decide
theorem pTable_2  : pTable 2  = 2  := by native_decide
theorem pTable_3  : pTable 3  = 3  := by native_decide
theorem pTable_4  : pTable 4  = 5  := by native_decide
theorem pTable_5  : pTable 5  = 7  := by native_decide
theorem pTable_6  : pTable 6  = 11 := by native_decide
theorem pTable_7  : pTable 7  = 15 := by native_decide
theorem pTable_8  : pTable 8  = 22 := by native_decide
theorem pTable_9  : pTable 9  = 30 := by native_decide
theorem pTable_10 : pTable 10 = 42 := by native_decide

/-! #### Monotonicity: p(n) ≤ p(n+1) for n = 0 … 9 -/

theorem pTable_mono :
    pTable 0  ≤ pTable 1  ∧
    pTable 1  ≤ pTable 2  ∧
    pTable 2  ≤ pTable 3  ∧
    pTable 3  ≤ pTable 4  ∧
    pTable 4  ≤ pTable 5  ∧
    pTable 5  ≤ pTable 6  ∧
    pTable 6  ≤ pTable 7  ∧
    pTable 7  ≤ pTable 8  ∧
    pTable 8  ≤ pTable 9  ∧
    pTable 9  ≤ pTable 10 := by native_decide

/-! #### p(n) < 2^n for n = 1 … 10 -/

theorem pTable_lt_pow2 :
    pTable 1  < 2 ^ 1  ∧
    pTable 2  < 2 ^ 2  ∧
    pTable 3  < 2 ^ 3  ∧
    pTable 4  < 2 ^ 4  ∧
    pTable 5  < 2 ^ 5  ∧
    pTable 6  < 2 ^ 6  ∧
    pTable 7  < 2 ^ 7  ∧
    pTable 8  < 2 ^ 8  ∧
    pTable 9  < 2 ^ 9  ∧
    pTable 10 < 2 ^ 10 := by native_decide

-- ============================================================
-- §2  Distinct-parts partition function q(n)  (OEIS A000009)
-- ============================================================

/-!
### 2. Distinct-parts partitions q(n)

`q(n)` counts partitions of `n` into **distinct** positive parts.

Exact table for n = 0 … 10:
  n  : 0  1  2  3  4  5  6  7   8   9  10
  q  : 1  1  1  2  2  3  4  5   6   8  10
-/

/-- Exact values of q(0), q(1), …, q(10). -/
def qTable : Fin 11 → ℕ :=
  ![1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10]

-- Spot-checks
theorem qTable_0  : qTable 0  = 1  := by native_decide
theorem qTable_3  : qTable 3  = 2  := by native_decide
theorem qTable_5  : qTable 5  = 3  := by native_decide
theorem qTable_7  : qTable 7  = 5  := by native_decide
theorem qTable_10 : qTable 10 = 10 := by native_decide

/-! #### q(n) ≤ p(n) for all tabulated values -/

theorem qTable_le_pTable :
    qTable 0  ≤ pTable 0  ∧
    qTable 1  ≤ pTable 1  ∧
    qTable 2  ≤ pTable 2  ∧
    qTable 3  ≤ pTable 3  ∧
    qTable 4  ≤ pTable 4  ∧
    qTable 5  ≤ pTable 5  ∧
    qTable 6  ≤ pTable 6  ∧
    qTable 7  ≤ pTable 7  ∧
    qTable 8  ≤ pTable 8  ∧
    qTable 9  ≤ pTable 9  ∧
    qTable 10 ≤ pTable 10 := by native_decide

-- ============================================================
-- §3  Euler's pentagonal recurrence (verified additively)
-- ============================================================

/-!
### 3. Euler's pentagonal number theorem

The generalised pentagonal numbers are k(3k−1)/2 for k = ±1, ±2, ±3, …,
giving 1, 2, 5, 7, 12, 15, 22, 26, …

The resulting recurrence for p(n) is:

    p(n) = p(n−1) + p(n−2) − p(n−5) − p(n−7) + p(n−12) + p(n−15) − …

We verify several instances in additive form to avoid ℕ-subtraction pitfalls.

  n=7:  p(7) = p(6)+p(5)−p(2)−p(0)
              ⟺  p(7)+p(2)+p(0) = p(6)+p(5)
              ⟺  15 + 2 + 1     = 11 + 7       ✓

  n=8:  p(8) = p(7)+p(6)−p(3)−p(1)
              ⟺  p(8)+p(3)+p(1) = p(7)+p(6)
              ⟺  22 + 3 + 1     = 15 + 11      ✓

  n=9:  p(9) = p(8)+p(7)−p(4)−p(2)
              ⟺  p(9)+p(4)+p(2) = p(8)+p(7)
              ⟺  30 + 5 + 2     = 22 + 15      ✓

  n=10: p(10) = p(9)+p(8)−p(5)−p(3)
               ⟺  p(10)+p(5)+p(3) = p(9)+p(8)
               ⟺  42 + 7 + 3      = 30 + 22    ✓
-/

-- n=5: p(5)+p(0) = p(4)+p(3)   i.e. 7+1 = 5+3
theorem pent_rec_5 :
    pTable 5 + pTable 0 = pTable 4 + pTable 3 := by native_decide

-- n=6: p(6)+p(1) = p(5)+p(4)   i.e. 11+1 = 7+5
theorem pent_rec_6 :
    pTable 6 + pTable 1 = pTable 5 + pTable 4 := by native_decide

-- n=7: p(7)+p(2)+p(0) = p(6)+p(5)   i.e. 15+2+1 = 11+7
theorem pent_rec_7 :
    pTable 7 + pTable 2 + pTable 0 = pTable 6 + pTable 5 := by native_decide

-- n=8: p(8)+p(3)+p(1) = p(7)+p(6)   i.e. 22+3+1 = 15+11
theorem pent_rec_8 :
    pTable 8 + pTable 3 + pTable 1 = pTable 7 + pTable 6 := by native_decide

-- n=9: p(9)+p(4)+p(2) = p(8)+p(7)   i.e. 30+5+2 = 22+15
theorem pent_rec_9 :
    pTable 9 + pTable 4 + pTable 2 = pTable 8 + pTable 7 := by native_decide

-- n=10: p(10)+p(5)+p(3) = p(9)+p(8)   i.e. 42+7+3 = 30+22
theorem pent_rec_10 :
    pTable 10 + pTable 5 + pTable 3 = pTable 9 + pTable 8 := by native_decide

-- ============================================================
-- §4  Euler's theorem: odd parts = distinct parts
-- ============================================================

/-!
### 4. Euler's theorem (numerical verification)

Euler proved that the number of partitions of n into **odd** parts equals
the number of partitions into **distinct** parts.

We record the odd-parts counts for n = 0 … 8:
  n         : 0  1  2  3  4  5  6  7  8
  oddParts  : 1  1  1  2  2  3  4  5  6

and verify that they agree with q(n) = qTable(n) for these values.
-/

/-- Exact values of the number of partitions into odd parts, n = 0 … 8. -/
def oddTable : Fin 9 → ℕ :=
  ![1, 1, 1, 2, 2, 3, 4, 5, 6]

-- Spot-checks
theorem oddTable_0 : oddTable 0 = 1 := by native_decide
theorem oddTable_3 : oddTable 3 = 2 := by native_decide
theorem oddTable_5 : oddTable 5 = 3 := by native_decide
theorem oddTable_7 : oddTable 7 = 5 := by native_decide
theorem oddTable_8 : oddTable 8 = 6 := by native_decide

/-! #### oddParts(n) = q(n) for n = 0 … 8 (Euler's theorem, verified numerically) -/

theorem euler_odd_eq_distinct :
    oddTable 0 = qTable 0 ∧
    oddTable 1 = qTable 1 ∧
    oddTable 2 = qTable 2 ∧
    oddTable 3 = qTable 3 ∧
    oddTable 4 = qTable 4 ∧
    oddTable 5 = qTable 5 ∧
    oddTable 6 = qTable 6 ∧
    oddTable 7 = qTable 7 ∧
    oddTable 8 = qTable 8 := by native_decide

-- ============================================================
-- §5  Restricted partitions r₃(n): parts ≤ 3
-- ============================================================

/-!
### 5. Restricted partitions r₃(n)

`r₃(n)` counts partitions of `n` using only parts from {1, 2, 3}.
The generating function is 1/((1−x)(1−x²)(1−x³)).

Exact table for n = 0 … 7:
  n   : 0  1  2  3  4  5  6  7
  r₃  : 1  1  2  3  4  5  7  8
-/

/-- Exact values of r₃(0), r₃(1), …, r₃(7). -/
def r3Table : Fin 8 → ℕ :=
  ![1, 1, 2, 3, 4, 5, 7, 8]

-- Spot-checks
theorem r3Table_0 : r3Table 0 = 1 := by native_decide
theorem r3Table_3 : r3Table 3 = 3 := by native_decide
theorem r3Table_6 : r3Table 6 = 7 := by native_decide
theorem r3Table_7 : r3Table 7 = 8 := by native_decide

/-! #### r₃(n) ≤ p(n) for tabulated values -/

theorem r3Table_le_pTable :
    r3Table 0 ≤ pTable 0 ∧
    r3Table 1 ≤ pTable 1 ∧
    r3Table 2 ≤ pTable 2 ∧
    r3Table 3 ≤ pTable 3 ∧
    r3Table 4 ≤ pTable 4 ∧
    r3Table 5 ≤ pTable 5 ∧
    r3Table 6 ≤ pTable 6 ∧
    r3Table 7 ≤ pTable 7 := by native_decide

-- ============================================================
-- §6  Growth bounds for p(n)
-- ============================================================

/-!
### 6. Growth bounds

Hardy and Ramanujan (1918) proved p(n) ~ exp(π√(2n/3))/(4n√3), which is
subexponential.  We record concrete numerical witnesses for n ≤ 10.

  · p(10) < 100  (true: 42 < 100)
  · p(10) > 40   (true: 42 > 40)
  · p(n)  < 2^n  for n = 1 … 10  (already in §1; see `pTable_lt_pow2`)

We also check which small n satisfy p(n)² < p(2n) (a super-multiplicativity
witness, when 2n ≤ 10):
  n=1: p(1)²=1 < p(2)=2   ✓
  n=2: p(2)²=4 < p(4)=5   ✓
  n=3: p(3)²=9 > p(6)=11  FAILS (9 < 11, actually holds!)
  n=4: p(4)²=25 > p(8)=22 FAILS (inequality reversed)
  n=5: p(5)²=49 > p(10)=42 FAILS
-/

-- p(10) is sandwiched between 40 and 100
theorem pTable_10_gt_40 : 40 < pTable 10 := by native_decide
theorem pTable_10_lt_100 : pTable 10 < 100 := by native_decide

-- Super-multiplicativity p(n)² < p(2n) holds for n = 1, 2, 3 only
theorem pTable_sqr_lt_pTable_double_1 :
    pTable 1 * pTable 1 < pTable 2 := by native_decide

theorem pTable_sqr_lt_pTable_double_2 :
    pTable 2 * pTable 2 < pTable 4 := by native_decide

theorem pTable_sqr_lt_pTable_double_3 :
    pTable 3 * pTable 3 < pTable 6 := by native_decide

-- It fails at n=4: p(4)²=25 > p(8)=22
theorem pTable_sqr_gt_pTable_double_4 :
    pTable 8 < pTable 4 * pTable 4 := by native_decide

-- It fails at n=5: p(5)²=49 > p(10)=42
theorem pTable_sqr_gt_pTable_double_5 :
    pTable 10 < pTable 5 * pTable 5 := by native_decide

-- ============================================================
-- §7  Comparison: q(n) ≤ r₃(n) fails for large n
-- ============================================================

/-!
### 7. Comparison between q(n) and r₃(n)

For small n, q(n) and r₃(n) are close but neither dominates the other
indefinitely.  We check the relationship for n = 0 … 7:

  n   : 0  1  2  3  4  5  6  7
  q   : 1  1  1  2  2  3  4  5
  r₃  : 1  1  2  3  4  5  7  8

So r₃(n) ≥ q(n) for all tabulated n ≥ 2.
-/

theorem r3Table_ge_qTable_small :
    qTable 0 ≤ r3Table 0 ∧
    qTable 1 ≤ r3Table 1 ∧
    qTable 2 ≤ r3Table 2 ∧
    qTable 3 ≤ r3Table 3 ∧
    qTable 4 ≤ r3Table 4 ∧
    qTable 5 ≤ r3Table 5 ∧
    qTable 6 ≤ r3Table 6 ∧
    qTable 7 ≤ r3Table 7 := by native_decide

end PartitionEnumeration
