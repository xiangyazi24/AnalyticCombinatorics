import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace CyclicStructures

open Finset

/-! ## Cyclic Structures and Burnside Counting

Necklaces (equivalence under cyclic rotation), bracelets (under the dihedral group),
primitive necklaces, and circular permutations.
Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter II. -/

/-- Euler's totient function: count of integers in [0, n) coprime to n. -/
def eulerTotient : Nat → Nat
  | 0 => 0
  | n => ((Finset.range n).filter (fun k => Nat.gcd n k = 1)).card

example : eulerTotient 1 = 1 := by native_decide
example : eulerTotient 2 = 1 := by native_decide
example : eulerTotient 4 = 2 := by native_decide
example : eulerTotient 6 = 2 := by native_decide
example : eulerTotient 12 = 4 := by native_decide

/-- Positive divisors of n. -/
def divisorsOf (n : Nat) : Finset Nat :=
  (Finset.range (n + 1)).filter (fun d => d > 0 ∧ n % d = 0)

example : divisorsOf 6 = {1, 2, 3, 6} := by native_decide
example : divisorsOf 12 = {1, 2, 3, 4, 6, 12} := by native_decide

/-- Necklace count via Burnside's lemma (Pólya enumeration):
    N(n,k) = (1/n) · Σ_{d|n} φ(n/d) · k^d -/
def necklaceCount (n k : Nat) : Nat :=
  if n = 0 then 0
  else ((divisorsOf n).sum (fun d => eulerTotient (n / d) * k ^ d)) / n

example : necklaceCount 1 2 = 2 := by native_decide
example : necklaceCount 2 2 = 3 := by native_decide
example : necklaceCount 3 2 = 4 := by native_decide
example : necklaceCount 4 2 = 6 := by native_decide
example : necklaceCount 5 2 = 8 := by native_decide
example : necklaceCount 6 2 = 14 := by native_decide
example : necklaceCount 7 2 = 20 := by native_decide
example : necklaceCount 8 2 = 36 := by native_decide

example : necklaceCount 1 3 = 3 := by native_decide
example : necklaceCount 2 3 = 6 := by native_decide
example : necklaceCount 3 3 = 11 := by native_decide
example : necklaceCount 4 3 = 24 := by native_decide

example : necklaceCount 0 5 = 0 := by native_decide
example : necklaceCount 10 1 = 1 := by native_decide

/-- The Burnside sum is always divisible by n (orbit-counting theorem). -/
theorem burnside_sum_divisible (n k : Nat) (hn : n > 0) :
    n ∣ (divisorsOf n).sum (fun d => eulerTotient (n / d) * k ^ d) := by
  sorry

/-- With one color, there is exactly one necklace for any positive length. -/
theorem necklaceCount_one_color (n : Nat) (hn : n > 0) :
    necklaceCount n 1 = 1 := by
  sorry

/-- For a single bead, the necklace count equals the number of colors. -/
theorem necklaceCount_one_bead (k : Nat) : necklaceCount 1 k = k := by
  sorry

/-- For prime p: N(p, k) = (k^p + (p-1)·k) / p. -/
theorem necklaceCount_prime (p k : Nat) (hp : Nat.Prime p) :
    necklaceCount p k = (k ^ p + (p - 1) * k) / p := by
  sorry

example : (2 ^ 5 + 4 * 2) / 5 = 8 := by native_decide
example : (2 ^ 7 + 6 * 2) / 7 = 20 := by native_decide

/-- Bracelet count: equivalence under the full dihedral group D_n. -/
def braceletCount (n k : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 1 then
    (necklaceCount n k + k ^ ((n + 1) / 2)) / 2
  else
    (2 * necklaceCount n k + k ^ (n / 2) + k ^ (n / 2 + 1)) / 4

example : braceletCount 1 2 = 2 := by native_decide
example : braceletCount 2 2 = 3 := by native_decide
example : braceletCount 3 2 = 4 := by native_decide
example : braceletCount 4 2 = 6 := by native_decide
example : braceletCount 5 2 = 8 := by native_decide
example : braceletCount 6 2 = 13 := by native_decide
example : braceletCount 7 2 = 18 := by native_decide
example : braceletCount 8 2 = 30 := by native_decide

example : braceletCount 4 3 = 21 := by native_decide
example : braceletCount 5 3 = 39 := by native_decide
example : braceletCount 6 3 = 92 := by native_decide

/-- Bracelets never exceed necklaces. -/
theorem bracelet_le_necklace (n k : Nat) :
    braceletCount n k ≤ necklaceCount n k := by
  sorry

/-- Circular permutations on n elements: (n-1)! -/
def circularPerms (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.factorial (n - 1)

example : circularPerms 1 = 1 := by native_decide
example : circularPerms 2 = 1 := by native_decide
example : circularPerms 3 = 2 := by native_decide
example : circularPerms 4 = 6 := by native_decide
example : circularPerms 5 = 24 := by native_decide
example : circularPerms 6 = 120 := by native_decide

/-- Circular permutations equal n!/n. -/
theorem circularPerms_eq_div (n : Nat) (hn : n > 0) :
    circularPerms n = Nat.factorial n / n := by
  sorry

/-- Primitive (aperiodic) necklace count via Möbius inversion:
    k^n = Σ_{d|n} d · M(d,k), solved recursively for M(n,k). -/
def primitiveNecklaceCount (n k : Nat) : Nat :=
  if n = 0 then 0
  else
    (k ^ n - (Finset.range n).sum (fun d =>
      if d > 0 ∧ d < n ∧ n % d = 0 then d * primitiveNecklaceCount d k else 0)) / n
termination_by n
decreasing_by omega

example : primitiveNecklaceCount 1 2 = 2 := by native_decide
example : primitiveNecklaceCount 2 2 = 1 := by native_decide
example : primitiveNecklaceCount 3 2 = 2 := by native_decide
example : primitiveNecklaceCount 4 2 = 3 := by native_decide
example : primitiveNecklaceCount 5 2 = 6 := by native_decide
example : primitiveNecklaceCount 6 2 = 9 := by native_decide

/-- Necklaces decompose: k^n = Σ_{d|n} d · M(d,k). -/
theorem string_primitive_decomposition (n k : Nat) (hn : n > 0) :
    k ^ n = (divisorsOf n).sum (fun d => d * primitiveNecklaceCount d k) := by
  sorry

/-- For prime p, primitive necklaces satisfy M(p,k) = (k^p - k) / p
    (connected to Fermat's little theorem). -/
theorem primitive_necklace_prime (p k : Nat) (hp : Nat.Prime p) :
    primitiveNecklaceCount p k = (k ^ p - k) / p := by
  sorry

example : 5 ∣ (2 ^ 5 - 2) := by native_decide
example : 7 ∣ (2 ^ 7 - 2) := by native_decide
example : 7 ∣ (3 ^ 7 - 3) := by native_decide
example : 11 ∣ (2 ^ 11 - 2) := by native_decide

/-- Surjective necklace count: necklaces of length n using exactly all k colors,
    computed via inclusion-exclusion on Burnside counts. -/
def surjectiveNecklaceCount (n k : Nat) : Nat :=
  if k = 0 then 0
  else
    let pos := (Finset.range (k + 1)).sum (fun j =>
      if j % 2 = 0 then Nat.choose k j * necklaceCount n (k - j) else 0)
    let neg := (Finset.range (k + 1)).sum (fun j =>
      if j % 2 = 1 then Nat.choose k j * necklaceCount n (k - j) else 0)
    pos - neg

example : surjectiveNecklaceCount 2 2 = 1 := by native_decide
example : surjectiveNecklaceCount 3 2 = 2 := by native_decide
example : surjectiveNecklaceCount 4 2 = 4 := by native_decide
example : surjectiveNecklaceCount 6 2 = 12 := by native_decide
example : surjectiveNecklaceCount 2 3 = 0 := by native_decide

end CyclicStructures
