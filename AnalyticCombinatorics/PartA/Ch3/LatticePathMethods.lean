import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace LatticePathMethods

/-! # Lattice Path Methods

Combinatorial identities and numerical verifications for lattice path counting,
from Flajolet & Sedgewick Chapters I and III. -/

/-! ## Delannoy Numbers

D(m,n) = number of paths from (0,0) to (m,n) using steps (1,0),(0,1),(1,1).
D(m,n) = Σ_{k=0}^{min(m,n)} C(m,k) * C(n,k) * 2^k. -/

def delannoy (m n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (min m n + 1), Nat.choose m k * Nat.choose n k * 2 ^ k

example : delannoy 0 0 = 1 := by native_decide
example : delannoy 1 1 = 3 := by native_decide
example : delannoy 2 2 = 13 := by native_decide
example : delannoy 3 3 = 63 := by native_decide
example : delannoy 4 4 = 321 := by native_decide

/-! ## Central Delannoy Numbers

D(n) = D(n,n): 1, 3, 13, 63, 321, 1683, 8989. -/

def centralDelannoy : Fin 7 → ℕ := ![1, 3, 13, 63, 321, 1683, 8989]

/-- Recurrence: (n+1)*D(n+1) = (6n+3)*D(n) - n*D(n-1).
    Verified for n=1: 2*13 = 9*3 - 1. -/
example : 2 * 13 = 9 * 3 - 1 := by native_decide
example : 3 * 63 = 15 * 13 - 2 * 3 := by native_decide

/-! ## Motzkin Numbers

Motzkin paths: paths from (0,0) to (n,0) using steps (1,1),(1,-1),(1,0),
never going below x-axis. Motzkin numbers: 1, 1, 2, 4, 9, 21, 51, 127. -/

def motzkinNumbers : Fin 8 → ℕ := ![1, 1, 2, 4, 9, 21, 51, 127]

/-! ## Narayana Numbers and Catalan

Narayana number N(n,k) = (1/n) * C(n,k) * C(n,k-1).
Sum of N(n,k) for k=1..n equals the Catalan number C_n.
N(6,1)=1, N(6,2)=15, N(6,3)=50, N(6,4)=50, N(6,5)=15, N(6,6)=1. Sum=132=C_6. -/

example : 1 + 15 + 50 + 50 + 15 + 1 = 132 := by native_decide

/-! ## Ballot Sequences (Bertrand's Reflection)

Catalan(n) = C(2n,n) - C(2n,n+1).
This counts the number of ballot sequences (Dyck paths) of semilength n. -/

example : Nat.choose 6 3 - Nat.choose 6 4 = 5 := by native_decide
example : Nat.choose 8 4 - Nat.choose 8 5 = 14 := by native_decide
example : Nat.choose 10 5 - Nat.choose 10 6 = 42 := by native_decide
example : Nat.choose 14 7 - Nat.choose 14 8 = 429 := by native_decide

/-! ## Trinomial Coefficients

T(n,k) = coefficient of x^k in (1+x+x²)^n.
Central trinomial T_n = [x^n](1+x+x²)^n: 1, 1, 3, 7, 19, 51.
Formula: T_n = Σ_{k=0}^{⌊n/2⌋} C(n,2k) * C(2k,k). -/

def centralTrinomial : Fin 6 → ℕ := ![1, 1, 3, 7, 19, 51]

/-- Verify T_3: C(3,0)*C(0,0) + C(3,2)*C(2,1) = 1 + 6 = 7. -/
example : 1 * 1 + 3 * 2 = 7 := by native_decide

end LatticePathMethods
