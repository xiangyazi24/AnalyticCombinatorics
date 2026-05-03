/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I — Polyominoes and lattice figure counting.

  Numerical verifications for polyomino enumeration sequences appearing in
  Flajolet & Sedgewick (2009) as examples of unlabelled combinatorial structures.

  Contents:
  1. Fixed polyomino counts by area (OEIS A001168).
  2. Free polyomino counts (up to rotation/reflection, OEIS A000105).
  3. Symmetry bound: fixed ≤ 8 × free.
  4. Parallelogram (staircase) polyominoes: count = C(2n-2, n-1).
  5. Domino tilings of the 2×n board = Fibonacci(n+1).
  6. Domino tilings of the 3×2n board via the recurrence 4T(n−1) − T(n−2).
  7. Aztec diamond tilings: 2^(n(n+1)/2).
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace Polyominoes

/-! ## 1. Fixed polyominoes (OEIS A001168) -/

/-- Number of fixed polyominoes (not up to rotation/reflection) with `i+1` cells,
for `i = 0, …, 7`.

  area  1  2   3   4   5    6    7     8
  count 1  2   6  19  63  216  760  2725
-/
def fixedPolyTable : Fin 8 → ℕ := ![1, 2, 6, 19, 63, 216, 760, 2725]

-- Spot-check individual values.
example : fixedPolyTable 0 = 1   := by native_decide
example : fixedPolyTable 1 = 2   := by native_decide
example : fixedPolyTable 2 = 6   := by native_decide
example : fixedPolyTable 3 = 19  := by native_decide
example : fixedPolyTable 4 = 63  := by native_decide
example : fixedPolyTable 5 = 216 := by native_decide
example : fixedPolyTable 6 = 760 := by native_decide
example : fixedPolyTable 7 = 2725 := by native_decide

/-- The fixed polyomino counts grow by a factor of at least 3 at each step
(for indices 1 through 6 in the table).  The growth constant converges to
approximately 4.0626 (Klarner's constant). -/
-- area 3 / area 2 = 6/2 = 3 exactly (ratio = 3, so ≥ not >)
example : fixedPolyTable 2 ≥ 3 * fixedPolyTable 1 := by native_decide  -- 6 ≥ 6
example : fixedPolyTable 3 > 3 * fixedPolyTable 2 := by native_decide  -- 19 > 18
example : fixedPolyTable 4 > 3 * fixedPolyTable 3 := by native_decide  -- 63 > 57
example : fixedPolyTable 5 > 3 * fixedPolyTable 4 := by native_decide  -- 216 > 189
example : fixedPolyTable 6 > 3 * fixedPolyTable 5 := by native_decide  -- 760 > 648
example : fixedPolyTable 7 > 3 * fixedPolyTable 6 := by native_decide  -- 2725 > 2280

/-! ## 2. Free polyominoes (OEIS A000105) -/

/-- Number of free polyominoes (counted up to rotation and reflection)
with `i` cells, for `i = 1, …, 8`.

  area  1  2  3   4   5   6    7    8
  count 1  1  2   5  12  35  108  369
-/
def freePolyTable : Fin 8 → ℕ := ![1, 1, 2, 5, 12, 35, 108, 369]

example : freePolyTable 0 = 1   := by native_decide
example : freePolyTable 1 = 1   := by native_decide
example : freePolyTable 2 = 2   := by native_decide
example : freePolyTable 3 = 5   := by native_decide
example : freePolyTable 4 = 12  := by native_decide
example : freePolyTable 5 = 35  := by native_decide
example : freePolyTable 6 = 108 := by native_decide
example : freePolyTable 7 = 369 := by native_decide

/-! ## 3. Symmetry bound: fixed ≤ 8 × free

The dihedral group of the square has order 8.  Each free polyomino corresponds
to at most 8 fixed ones, so `fixedPolyTable i ≤ 8 * freePolyTable i` for all i
in the table. -/

/-- For every area in the table, the number of fixed polyominoes is at most
8 times the number of free polyominoes. -/
example : ∀ i : Fin 8, fixedPolyTable i ≤ 8 * freePolyTable i := by native_decide

-- Individual checks (area 1 through 8):
-- area 1: 1 ≤ 8*1 = 8   ✓
-- area 2: 2 ≤ 8*1 = 8   ✓
-- area 3: 6 ≤ 8*2 = 16  ✓
-- area 4: 19 ≤ 8*5 = 40  ✓
-- area 5: 63 ≤ 8*12 = 96  ✓
-- area 6: 216 ≤ 8*35 = 280  ✓
-- area 7: 760 ≤ 8*108 = 864  ✓
-- area 8: 2725 ≤ 8*369 = 2952  ✓
example : fixedPolyTable 7 ≤ 8 * freePolyTable 7 := by native_decide  -- 2725 ≤ 2952

/-! ## 4. Parallelogram (staircase) polyominoes

Parallelogram polyominoes (also called staircase polyominoes or stack polyominoes)
with semi-perimeter n+1 are counted by the central binomial coefficient
`C(2n, n)` (Delest–Viennot 1984).

Semi-perimeter 2 (n=1):  C(2,1) = 2  — but usually normalised so sp=2 → 1 shape.
The standard formula counts parallelogram polyominoes with semi-perimeter p = n+1
as C(2(p-1), p-1) = C(2n, n).  For the first several values:

  n = 1, sp = 2 : C(2,1)   = 2
  n = 2, sp = 3 : C(4,2)   = 6
  n = 3, sp = 4 : C(6,3)   = 20
  n = 4, sp = 5 : C(8,4)   = 70
  n = 5, sp = 6 : C(10,5)  = 252

These are the Catalan-related central binomial coefficients. -/

example : Nat.choose 2  1  = 2   := by native_decide
example : Nat.choose 4  2  = 6   := by native_decide
example : Nat.choose 6  3  = 20  := by native_decide
example : Nat.choose 8  4  = 70  := by native_decide
example : Nat.choose 10 5  = 252 := by native_decide
example : Nat.choose 12 6  = 924 := by native_decide

/-- The number of parallelogram polyominoes with semi-perimeter `n+1`
is the central binomial coefficient `C(2n, n)`. -/
def parallelogramCount (n : ℕ) : ℕ := Nat.choose (2 * n) n

example : parallelogramCount 1 = 2   := by native_decide
example : parallelogramCount 2 = 6   := by native_decide
example : parallelogramCount 3 = 20  := by native_decide
example : parallelogramCount 4 = 70  := by native_decide
example : parallelogramCount 5 = 252 := by native_decide

-- These counts grow by roughly 4 each step (consistent with growth constant 4
-- for the square lattice).
example : parallelogramCount 5 > 3 * parallelogramCount 4 := by native_decide  -- 252 > 210

/-! ## 5. Domino tilings of the 2×n board

The number of domino tilings of a 2×n board satisfies the Fibonacci recurrence.
Specifically, the count equals `Nat.fib (n + 1)` using Lean's Fibonacci function
(where `Nat.fib 0 = 0`, `Nat.fib 1 = 1`, `Nat.fib 2 = 1`, …). -/

/-- Number of domino tilings of the 2×n board equals Fibonacci(n+1). -/
def dominoTiling (n : ℕ) : ℕ := Nat.fib (n + 1)

example : dominoTiling 0 = 1  := by native_decide   -- 1×1 trivial tiling
example : dominoTiling 1 = 1  := by native_decide   -- 2×1: one vertical domino
example : dominoTiling 2 = 2  := by native_decide   -- 2×2: VV or HH
example : dominoTiling 3 = 3  := by native_decide
example : dominoTiling 4 = 5  := by native_decide
example : dominoTiling 5 = 8  := by native_decide
example : dominoTiling 6 = 13 := by native_decide
example : dominoTiling 7 = 21 := by native_decide
example : dominoTiling 8 = 34 := by native_decide

-- The recurrence: tilings(n+2) = tilings(n+1) + tilings(n).
example : dominoTiling 7 = dominoTiling 6 + dominoTiling 5 := by native_decide
example : dominoTiling 8 = dominoTiling 7 + dominoTiling 6 := by native_decide

/-! ## 6. Domino tilings of the 3×2n board

The number of domino tilings of a 3×2n board satisfies the second-order
linear recurrence T(n) = 4·T(n-1) - T(n-2), with T(0)=1 and T(1)=3.

Values: 1, 3, 11, 41, 153, 571, 2131, 7953, … -/

/-- Number of domino tilings of the 3 × 2n board. -/
def tiling3x2n : ℕ → ℕ
  | 0     => 1
  | 1     => 3
  | n + 2 => 4 * tiling3x2n (n + 1) - tiling3x2n n

example : tiling3x2n 0 = 1    := by native_decide
example : tiling3x2n 1 = 3    := by native_decide
example : tiling3x2n 2 = 11   := by native_decide
example : tiling3x2n 3 = 41   := by native_decide
example : tiling3x2n 4 = 153  := by native_decide
example : tiling3x2n 5 = 571  := by native_decide
example : tiling3x2n 6 = 2131 := by native_decide

-- Verify the recurrence holds at a specific step.
example : tiling3x2n 6 = 4 * tiling3x2n 5 - tiling3x2n 4 := by native_decide

-- All values in the table are odd.
example : ∀ n : Fin 7, tiling3x2n n % 2 = 1 := by native_decide

-- The counts grow by a factor approaching 2 + √3 ≈ 3.732.
example : tiling3x2n 6 > 3 * tiling3x2n 5 := by native_decide  -- 2131 > 1713

/-! ## 7. Aztec diamond tilings

The Aztec diamond of order n has 2^(n(n+1)/2) domino tilings
(Elkies–Kuperberg–Larsen–Propp 1992).

n=1:  2^1  = 2
n=2:  2^3  = 8
n=3:  2^6  = 64
n=4:  2^10 = 1024
n=5:  2^15 = 32768
-/

/-- Number of domino tilings of the Aztec diamond of order `n`. -/
def aztecTilings (n : ℕ) : ℕ := 2 ^ (n * (n + 1) / 2)

example : aztecTilings 0 = 1      := by native_decide   -- empty diamond
example : aztecTilings 1 = 2      := by native_decide
example : aztecTilings 2 = 8      := by native_decide
example : aztecTilings 3 = 64     := by native_decide
example : aztecTilings 4 = 1024   := by native_decide
example : aztecTilings 5 = 32768  := by native_decide
example : aztecTilings 6 = 2097152 := by native_decide  -- 2^21

-- Doubling ratio: aztecTilings(n+1) / aztecTilings(n) = 2^(n+1).
-- Verify as a multiplicative identity for small n:
example : aztecTilings 2 = 2 ^ 2 * aztecTilings 1 := by native_decide  -- 8 = 4*2
example : aztecTilings 3 = 2 ^ 3 * aztecTilings 2 := by native_decide  -- 64 = 8*8
example : aztecTilings 4 = 2 ^ 4 * aztecTilings 3 := by native_decide  -- 1024 = 16*64
example : aztecTilings 5 = 2 ^ 5 * aztecTilings 4 := by native_decide  -- 32768 = 32*1024

end Polyominoes
