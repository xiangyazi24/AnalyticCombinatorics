import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace GeneratingFunctionOps

/-! # Generating Function Operations and Coefficient Sequences

This file formalizes the principal operations on generating functions and their
effects on coefficient sequences, as treated in Flajolet & Sedgewick Chapter III:

- **Pointing / marking**: z·d/dz multiplies coefficients by index n
- **Sequence operations**: left/right shift, partial sums
- **Convolution**: product of GFs corresponds to discrete convolution of sequences
- **Hadamard product**: coefficient-wise multiplication
- **Composition**: substitution A(B(z)) and its coefficient sequences
- **Compositional inverse**: functional inverse of GFs

All proofs are via `native_decide`, `decide`, `norm_num`, or `omega`.
-/

/-! ## 1. Pointing / Marking Operator

The pointing operator theta = z*d/dz acts on a GF A(z) = sum a_n z^n to give
Theta[A](z) = sum n*a_n z^n.  In combinatorics this "marks" one element
of each structure, so the coefficient at index n is multiplied by n. -/

/-- Pointed geometric series: if a(n) = 1 for all n,
    then Theta[A](n) = n (the derivative of 1/(1-z) is z/(1-z)^2). -/
def geomSeq : Fin 10 → ℕ := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def pointedGeom : Fin 10 → ℕ := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- Pointing multiplies each coefficient by its index. -/
example : ∀ i : Fin 10, pointedGeom i = (i : ℕ) * geomSeq i := by native_decide

/-- Pointed geometric coefficient at index 7 is 7. -/
example : pointedGeom 7 = 7 := by native_decide

/-- Central binomial coefficients C(2n,n) for n = 0..8.
    These equal (n+1)*C(n) where C(n) is the Catalan number,
    confirming the pointing formula for the Catalan GF. -/
def centralBinom : Fin 9 → ℕ := ![1, 2, 6, 20, 70, 252, 924, 3432, 12870]

/-- Verify central binomials against the choose function. -/
example : ∀ i : Fin 9, centralBinom i = choose (2 * (i : ℕ)) (i : ℕ) := by native_decide

/-- Catalan numbers C(n) = C(2n,n)/(n+1) for n = 0..8. -/
def catalanSeq : Fin 9 → ℕ := ![1, 1, 2, 5, 14, 42, 132, 429, 1430]

/-- Catalan numbers satisfy C(2n,n) = (n+1)*C(n).
    Pointing the Catalan GF gives back the central binomial coefficients. -/
example : ∀ i : Fin 9, centralBinom i = ((i : ℕ) + 1) * catalanSeq i := by native_decide

/-- C(2n,n) is divisible by n+1 for all n = 0..8 (Catalan integrality). -/
example : ∀ i : Fin 9, ((i : ℕ) + 1) ∣ centralBinom i := by native_decide

/-- C(2*4, 4) = 70 and C(4) = 14, so 5 * 14 = 70. -/
example : centralBinom 4 = 5 * catalanSeq 4 := by native_decide

/-! ## 2. Sequence Operations

### Left shift (divide by z)
If A(z) = sum a_n z^n then A(z)/z = sum a_{n+1} z^n (dropping a_0 = 0 term).
Shifts the index down by 1: the n-th coefficient of the shifted sequence is a_{n+1}.

### Right shift (multiply by z)
Multiplying by z prepends a 0 to the coefficient sequence.

### Partial sums
If B(z) = A(z)/(1-z) then b_n = sum_{k=0}^n a_k. -/

/-- Fibonacci sequence for n = 0..9: F(0)=0, F(1)=1, F(2)=1, ... -/
def fibSeq : Fin 10 → ℕ := ![0, 1, 1, 2, 3, 5, 8, 13, 21, 34]

/-- Fibonacci extended to 11 terms. -/
def fibSeq11 : Fin 11 → ℕ := ![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]

/-- Left shift of Fibonacci: shifted(n) = F(n+1).
    Sequence: 1, 1, 2, 3, 5, 8, 13, 21, 34, 55. -/
def fibShifted : Fin 10 → ℕ := ![1, 1, 2, 3, 5, 8, 13, 21, 34, 55]

/-- Left shift corresponds to index increment: fibShifted(n) = fibSeq11(n+1). -/
example : ∀ i : Fin 10,
    fibShifted i = fibSeq11 ⟨(i : ℕ) + 1, by omega⟩ := by native_decide

/-- Fibonacci left shift recurrence is preserved. -/
example : ∀ n : Fin 8,
    fibShifted ⟨n + 2, by omega⟩ =
    fibShifted ⟨n + 1, by omega⟩ + fibShifted ⟨n, by omega⟩ := by native_decide

/-- Right shift of constant sequence: prepend 0.
    If a(n) = 1 for n >= 0, then right-shifted b(0) = 0, b(n) = 1 for n >= 1. -/
def rightShiftConst : Fin 9 → ℕ := ![0, 1, 1, 1, 1, 1, 1, 1, 1]

/-- Right shift prepends zero. -/
example : rightShiftConst 0 = 0 := by native_decide
example : ∀ i : Fin 8, rightShiftConst ⟨(i : ℕ) + 1, by omega⟩ = 1 := by native_decide

/-- Partial sums of constant sequence: if a(n) = 1, then partial sums = n+1.
    (This is A(z)/(1-z) with A(z) = 1/(1-z), giving 1/(1-z)^2.) -/
def partialSumConst : Fin 10 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

example : ∀ i : Fin 10, partialSumConst i = (i : ℕ) + 1 := by native_decide

/-- Partial sums check: each entry equals sum of geomSeq up to that index. -/
example : ∀ i : Fin 10,
    partialSumConst i = ∑ k : Fin ((i : ℕ) + 1), geomSeq ⟨k, by omega⟩ := by
  native_decide

/-- Partial sums of a(n) = n give triangular numbers: T(n) = n(n+1)/2.
    Table for n = 0..9: 0, 1, 3, 6, 10, 15, 21, 28, 36, 45. -/
def naturalSeq : Fin 10 → ℕ := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
def triangularTab : Fin 10 → ℕ := ![0, 1, 3, 6, 10, 15, 21, 28, 36, 45]

/-- Triangular numbers formula: T(n) = n*(n+1)/2. -/
example : ∀ i : Fin 10, 2 * triangularTab i = (i : ℕ) * ((i : ℕ) + 1) := by native_decide

/-- Triangular numbers are partial sums of natural numbers. -/
example : ∀ i : Fin 10,
    triangularTab i = ∑ k : Fin ((i : ℕ) + 1), (k : ℕ) := by
  native_decide

/-- Triangular numbers satisfy T(n) = T(n-1) + n. -/
example : ∀ n : Fin 9,
    triangularTab ⟨n + 1, by omega⟩ = triangularTab ⟨n, by omega⟩ + (n + 1) := by
  native_decide

/-! ## 3. Convolution (Product of GFs)

If A(z) = sum a_n z^n and B(z) = sum b_n z^n, then
[z^n](A(z)*B(z)) = sum_{k=0}^n a_k * b_{n-k}.

This is the discrete convolution of sequences a and b. -/

/-- Convolution of two constant-1 sequences gives n+1.
    [z^n](1/(1-z)^2) = n+1. -/
def convOneOne : Fin 10 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- 1 * 1 convolution: (a*a)(n) = sum_{k=0}^n 1*1 = n+1. -/
example : ∀ i : Fin 10,
    convOneOne i = ∑ _ : Fin ((i : ℕ) + 1), (1 : ℕ) := by
  native_decide

example : ∀ i : Fin 10, convOneOne i = (i : ℕ) + 1 := by native_decide

/-- Fibonacci sequence extended to 12 terms for convolution use. -/
def fibSeq12 : Fin 12 → ℕ := ![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]

/-- Fibonacci self-convolution (F*F)(n) = sum_{k=0}^n F(k)*F(n-k).
    Values for n=0..5: 0, 0, 1, 2, 5, 10. -/
def fibConvFib : Fin 6 → ℕ := ![0, 0, 1, 2, 5, 10]

/-- Helper: compute Fibonacci convolution at a specific index using a bounded sum. -/
def fibConv (n : Fin 6) : ℕ :=
  ∑ k : Fin ((n : ℕ) + 1), fibSeq12 ⟨k, by omega⟩ * fibSeq12 ⟨(n : ℕ) - k, by omega⟩

/-- Verify Fibonacci self-convolution table against the formula. -/
example : fibConv 0 = 0 := by native_decide
example : fibConv 1 = 0 := by native_decide
example : fibConv 2 = 1 := by native_decide
example : fibConv 3 = 2 := by native_decide
example : fibConv 4 = 5 := by native_decide
example : fibConv 5 = 10 := by native_decide

/-- fibConvFib table matches formula. -/
example : ∀ i : Fin 6, fibConvFib i = fibConv i := by native_decide

/-- Catalan sequence extended to 10 terms for convolution use. -/
def catalanSeq10 : Fin 10 → ℕ := ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]

/-- Catalan self-convolution: (C*C)(n) = C(n+1).
    Catalan convolution C(n+1) = sum_{k=0}^n C(k)*C(n-k), verified for n = 0..5. -/
def catalanConv : Fin 6 → ℕ := ![1, 2, 5, 14, 42, 132]

/-- Helper: compute Catalan convolution at a specific index. -/
def catConv (n : Fin 6) : ℕ :=
  ∑ k : Fin ((n : ℕ) + 1),
    catalanSeq10 ⟨k, by omega⟩ * catalanSeq10 ⟨(n : ℕ) - k, by omega⟩

/-- Verify Catalan self-convolution equals C(n+1) for n = 0..5. -/
example : catConv 0 = catalanSeq10 1 := by native_decide
example : catConv 1 = catalanSeq10 2 := by native_decide
example : catConv 2 = catalanSeq10 3 := by native_decide
example : catConv 3 = catalanSeq10 4 := by native_decide
example : catConv 4 = catalanSeq10 5 := by native_decide
example : catConv 5 = catalanSeq10 6 := by native_decide

/-- The catalanConv table matches catConv. -/
example : ∀ i : Fin 6, catalanConv i = catConv i := by native_decide

/-- Catalan convolution identity: catalanConv(n) = C(n+1) for all n = 0..5. -/
example : ∀ i : Fin 6, catalanConv i = catalanSeq10 ⟨(i : ℕ) + 1, by omega⟩ := by
  native_decide

/-- Catalan C(0)*C(0) = 1 = C(1). -/
example : catalanSeq 0 * catalanSeq 0 = catalanSeq 1 := by native_decide

/-- Catalan two-term convolution: C(0)*C(1) + C(1)*C(0) = 2 = C(2). -/
example : catalanSeq 0 * catalanSeq 1 + catalanSeq 1 * catalanSeq 0 = catalanSeq 2 := by
  native_decide

/-! ## 4. Hadamard Product (Coefficient-wise Multiplication)

The Hadamard product (a o b) of two sequences is defined coefficient-wise:
(a o b)(n) = a(n) * b(n).  At the level of GFs this corresponds to a
Hadamard convolution integral, but at the coefficient level it is simply
pointwise multiplication. -/

/-- Hadamard product n o n = n^2 for n = 0..8. -/
def squaresTab : Fin 9 → ℕ := ![0, 1, 4, 9, 16, 25, 36, 49, 64]

/-- Squares are the Hadamard product of natural numbers with themselves. -/
example : ∀ i : Fin 9, squaresTab i = (i : ℕ) * (i : ℕ) := by native_decide

/-- Square numbers are non-decreasing. -/
example : ∀ n : Fin 8,
    squaresTab ⟨n, by omega⟩ ≤ squaresTab ⟨n + 1, by omega⟩ := by native_decide

/-- Hadamard product of Catalan with constant 1 is Catalan (identity element). -/
example : ∀ i : Fin 9, catalanSeq i * 1 = catalanSeq i := by native_decide

/-- Hadamard product 2^n o n = n * 2^n for n = 0..8.
    Table: 0, 2, 8, 24, 64, 160, 384, 896, 2048. -/
def twoPowSeq : Fin 9 → ℕ := ![1, 2, 4, 8, 16, 32, 64, 128, 256]
def nTwoPow : Fin 9 → ℕ := ![0, 2, 8, 24, 64, 160, 384, 896, 2048]

/-- Verify n * 2^n table. -/
example : ∀ i : Fin 9, nTwoPow i = (i : ℕ) * twoPowSeq i := by native_decide

/-- 2^n table values are powers of 2. -/
example : ∀ i : Fin 9, twoPowSeq i = 2 ^ (i : ℕ) := by native_decide

/-- n * 2^n values verify: 0, 2, 8, 24, 64, 160, 384, 896, 2048. -/
example : nTwoPow 0 = 0 := by native_decide
example : nTwoPow 1 = 2 := by native_decide
example : nTwoPow 4 = 64 := by native_decide
example : nTwoPow 8 = 2048 := by native_decide

/-- n * 2^n satisfies the recurrence (n+1)*2^{n+1} = 2*(n*2^n) + 2^{n+1}. -/
example : ∀ n : Fin 8,
    nTwoPow ⟨n + 1, by omega⟩ =
    2 * nTwoPow ⟨n, by omega⟩ + twoPowSeq ⟨n + 1, by omega⟩ := by native_decide

/-! ## 5. Composition (Substitution) A(B(z))

If A(z) = sum a_n z^n and B(z) has B(0) = 0, then
A(B(z)) = sum a_n B(z)^n gives a well-defined formal power series.

Key example: A(z) = 1/(1-z), B(z) = z/(1-z).
Then A(B(z)) = 1/(1 - z/(1-z)) = 1/(1-2z), coefficients = 2^n. -/

/-- Powers of 2: coefficients of 1/(1-2z) for n = 0..10. -/
def powersOf2 : Fin 11 → ℕ := ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

/-- Powers of 2 are exactly 2^n. -/
example : ∀ i : Fin 11, powersOf2 i = 2 ^ (i : ℕ) := by native_decide

/-- Composition identity: 2^{n+1} = 2 * 2^n (recurrence from 1/(1-2z)). -/
example : ∀ n : Fin 10,
    powersOf2 ⟨n + 1, by omega⟩ = 2 * powersOf2 ⟨n, by omega⟩ := by native_decide

/-- Sum of first n+1 powers of 2 = 2^{n+1} - 1.
    Verified for n = 0..9 (using n < 10 so n+1 < 11). -/
example : ∀ i : Fin 10,
    ∑ k : Fin ((i : ℕ) + 1), powersOf2 ⟨k, by omega⟩ =
    powersOf2 ⟨(i : ℕ) + 1, by omega⟩ - 1 := by native_decide

/-- Bell numbers B(n) arise as coefficients of exp(e^z - 1).
    Values for n = 0..7: 1, 1, 2, 5, 15, 52, 203, 877. -/
def bellTab : Fin 8 → ℕ := ![1, 1, 2, 5, 15, 52, 203, 877]

/-- Bell numbers are positive. -/
example : ∀ i : Fin 8, 0 < bellTab i := by native_decide

/-- Bell number recurrence: B(n+1) = sum_{k=0}^n C(n,k) * B(k), verified for n=0..5.
    Uses bounded sum with Fin to avoid out-of-bounds on the Bell table. -/
def bellConv (n : Fin 7) : ℕ :=
  ∑ k : Fin ((n : ℕ) + 1), choose (n : ℕ) k * bellTab ⟨k, by omega⟩

/-- Verify Bell recurrence for n = 0..5. -/
example : bellConv 0 = bellTab 1 := by native_decide
example : bellConv 1 = bellTab 2 := by native_decide
example : bellConv 2 = bellTab 3 := by native_decide
example : bellConv 3 = bellTab 4 := by native_decide
example : bellConv 4 = bellTab 5 := by native_decide
example : bellConv 5 = bellTab 6 := by native_decide

/-- Bell numbers: B(6) = 203, B(7) = 877. -/
example : bellTab 6 = 203 := by native_decide
example : bellTab 7 = 877 := by native_decide

/-- Bell numbers are non-decreasing after index 1. -/
example : ∀ n : Fin 6, bellTab ⟨n + 1, by omega⟩ ≤ bellTab ⟨n + 2, by omega⟩ := by
  native_decide

/-! ## 6. Compositional Inverse

If B(A(z)) = z (or A(B(z)) = z), then B is the compositional inverse of A.
This is related to Lagrange inversion and tree enumeration. -/

/-- Catalan GF functional equation: C(n+1) = sum_{k=0}^n C(k)*C(n-k).
    This verifies C(z) = 1 + z*C(z)^2 at the coefficient level. -/
example : ∀ i : Fin 6, catalanConv i = catConv i := by native_decide

/-- n^{n-1} for n = 1..6: 1, 2, 9, 64, 625, 7776.
    These count labelled rooted trees on n vertices (Cayley's formula). -/
def treeNumerators : Fin 6 → ℕ := ![1, 2, 9, 64, 625, 7776]

/-- Verify n^{n-1} values individually. -/
example : treeNumerators 0 = 1 ^ 0 := by native_decide
example : treeNumerators 1 = 2 ^ 1 := by native_decide
example : treeNumerators 2 = 3 ^ 2 := by native_decide
example : treeNumerators 3 = 4 ^ 3 := by native_decide
example : treeNumerators 4 = 5 ^ 4 := by native_decide
example : treeNumerators 5 = 6 ^ 5 := by native_decide

/-- treeNumerators(i) = (i+1)^i (n = i+1, so n^{n-1} = (i+1)^i). -/
example : ∀ i : Fin 6, treeNumerators i = ((i : ℕ) + 1) ^ (i : ℕ) := by native_decide

/-- Tree numerators are strictly increasing. -/
example : ∀ n : Fin 5,
    treeNumerators ⟨n, by omega⟩ < treeNumerators ⟨n + 1, by omega⟩ := by native_decide

/-- The number of labelled rooted forests on n labelled nodes
    equals (n+1)^{n-1}, by Cayley's generalization. For n=1..5: 1, 3, 16, 125, 1296. -/
def forestNumerators : Fin 5 → ℕ := ![1, 3, 16, 125, 1296]

/-- Forest count (n+1)^{n-1}: forestNumerators(i) = (i+2)^i for i = 0..4. -/
example : ∀ i : Fin 5, forestNumerators i = ((i : ℕ) + 2) ^ (i : ℕ) := by native_decide

/-! ## 7. Summary: Operations and Their Effects

Collection of small numerical checks tying together the operations. -/

/-- Pointing preserves the Catalan recurrence structure:
    (n+1)*C(n) = C(2n,n), verified for n = 0..8. -/
example : ∀ i : Fin 9, (i : ℕ) * catalanSeq i + catalanSeq i = centralBinom i := by
  native_decide

/-- Partial sums of Catalan: sum_{k=0}^n C(k) for n=0..7. -/
def catalanPartialSums : Fin 8 → ℕ := ![1, 2, 4, 9, 23, 65, 197, 626]

/-- Catalan partial sums satisfy PSC(n) = sum_{k=0}^n C(k). -/
example : ∀ i : Fin 8,
    catalanPartialSums i = ∑ k : Fin ((i : ℕ) + 1), catalanSeq ⟨k, by omega⟩ := by
  native_decide

/-- Fibonacci partial sums: PSF(n) = sum_{k=0}^n F(k) for n = 0..8. -/
def fibPartialSums : Fin 9 → ℕ := ![0, 1, 2, 4, 7, 12, 20, 33, 54]

/-- Fibonacci partial sums are correct sums. -/
example : ∀ i : Fin 9,
    fibPartialSums i = ∑ k : Fin ((i : ℕ) + 1), fibSeq ⟨k, by omega⟩ := by
  native_decide

/-- Identity: sum_{k=0}^n F(k) = F(n+2) - 1 (Fibonacci partial sum identity).
    Verified for n = 0..8. -/
example : ∀ i : Fin 9,
    fibPartialSums i = fibSeq11 ⟨(i : ℕ) + 2, by omega⟩ - 1 := by native_decide

/-- Odd numbers: 1, 3, 5, 7, 9, 11, 13, 15, 17. -/
def oddTab : Fin 9 → ℕ := ![1, 3, 5, 7, 9, 11, 13, 15, 17]

/-- Differences of consecutive squares are consecutive odd numbers. -/
example : ∀ n : Fin 8,
    squaresTab ⟨n + 1, by omega⟩ - squaresTab ⟨n, by omega⟩ = 2 * (n : ℕ) + 1 := by
  native_decide

/-- oddTab(n) = 2n+1. -/
example : ∀ i : Fin 9, oddTab i = 2 * (i : ℕ) + 1 := by native_decide

/-- Sum of first n odd numbers = n^2: sum_{k=0}^{n-1} (2k+1) = n^2. -/
example : ∀ i : Fin 9,
    squaresTab i = ∑ k : Fin (i : ℕ), (2 * (k : ℕ) + 1) := by native_decide

end GeneratingFunctionOps
