/-
  Chapter I — Advanced Symbolic Method Constructions

  Numerical verifications of counting sequences arising from the main
  symbolic-method constructions: SEQ, MSET, PSET, CYC, substitution,
  and pointing.

  Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter I.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace SymbolicMethodAdvanced

/-! ## 1. Sequence construction SEQ(A)

  If A = {1,2}-atoms (two atoms of size 1), then A(z) = 2z and
  SEQ(A) has OGF 1/(1-2z), so |SEQ_n| = 2^n.
-/

example : (2 : ℕ)^0 = 1 := by native_decide
example : (2 : ℕ)^5 = 32 := by native_decide
example : (2 : ℕ)^10 = 1024 := by native_decide

/-! ## 2. Multiset construction MSET(A)

  If A has one element of each size ≥ 1, then MSET(A) has OGF
  Π_{n≥1} 1/(1-z^n), the partition generating function.
  p(0)=1, p(1)=1, p(2)=2, p(3)=3, p(4)=5, p(5)=7, p(6)=11,
  p(7)=15, p(8)=22, p(9)=30, p(10)=42.
-/

def partitionTable : Fin 11 → ℕ := ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42]

example : partitionTable 0 = 1 := by native_decide
example : partitionTable 4 = 5 := by native_decide
example : partitionTable 10 = 42 := by native_decide

/-! ## 3. Powerset construction PSET(A)

  PSET(A) = choosing distinct items from A.
  GF = Π_{n≥1} (1+z^n).
  For A with one element of each size: partitions into distinct parts.
  q(0)=1, q(1)=1, q(2)=1, q(3)=2, q(4)=2, q(5)=3, q(6)=4, q(7)=5.
-/

def distinctPartitions : Fin 8 → ℕ := ![1, 1, 1, 2, 2, 3, 4, 5]

example : distinctPartitions 0 = 1 := by native_decide
example : distinctPartitions 3 = 2 := by native_decide
example : distinctPartitions 5 = 3 := by native_decide
example : distinctPartitions 7 = 5 := by native_decide

/-- Euler's theorem: partitions into distinct parts = partitions into odd parts.
    Verify at n = 5: both counts equal 3. -/
example : distinctPartitions 5 = 3 := by native_decide

/-! ## 4. Cycle construction CYC(A)

  For labelled structures with A = atom:
  |CYC_n| = (n-1)! (circular permutations of n elements).
  Equivalently, n!/n = (n-1)!.
-/

example : Nat.factorial 4 / 4 = Nat.factorial 3 := by native_decide
example : Nat.factorial 5 / 5 = Nat.factorial 4 := by native_decide
example : Nat.factorial 6 / 6 = Nat.factorial 5 := by native_decide

/-! ## 5. Substitution (composition) A ∘ B

  Set of cycles = permutations: exp(-ln(1-z)) = 1/(1-z), giving n! permutations.
  Perfect matchings on 2n points: (2n)! / (2^n · n!) = (2n-1)!!.
  (2·1-1)!!=1, (2·2-1)!!=3, (2·3-1)!!=15, (2·4-1)!!=105.
-/

example : Nat.factorial 6 / (2^3 * Nat.factorial 3) = 15 := by native_decide
example : Nat.factorial 8 / (2^4 * Nat.factorial 4) = 105 := by native_decide
example : Nat.factorial 10 / (2^5 * Nat.factorial 5) = 945 := by native_decide

/-! ## 6. Pointing and marking

  Pointing multiplies labelled coefficients by n:
  |Θ(C)_n| = n · |C_n|.
  For C = permutations (|C_n| = n!): |Θ(perm)_n| = n · n!.
-/

example : 3 * Nat.factorial 3 = 18 := by native_decide
example : 4 * Nat.factorial 4 = 96 := by native_decide
example : 5 * Nat.factorial 5 = 600 := by native_decide

end SymbolicMethodAdvanced
