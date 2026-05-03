import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace WalksCounting

/-! # Walks Counting

Numerical verifications for random walks and lattice path counting,
based on Flajolet & Sedgewick Chapters I and III. -/

/-! ## 1. Ballot Problem: Catalan Numbers

The number of paths from (0,0) to (2n,0) that stay ≥ 0 equals
  C(2n, n) / (n+1) = Catalan(n).
-/

-- Catalan(3) = C(6,3)/4 = 20/4 = 5
example : Nat.choose 6 3 / 4 = 5 := by native_decide

-- Catalan(4) = C(8,4)/5 = 70/5 = 14
example : Nat.choose 8 4 / 5 = 14 := by native_decide

-- Catalan(5) = C(10,5)/6 = 252/6 = 42
example : Nat.choose 10 5 / 6 = 42 := by native_decide

-- Catalan(6) = C(12,6)/7 = 924/7 = 132
example : Nat.choose 12 6 / 7 = 132 := by native_decide

-- Catalan(7) = C(14,7)/8 = 3432/8 = 429
example : Nat.choose 14 7 / 8 = 429 := by native_decide

-- Ballot formula: paths staying non-negative from (0,0) to (m+n, m-n)
-- = C(m+n,m) - C(m+n,m+1)  (Bertrand ballot).
-- Check m=4, n=0: C(4,4) - C(4,5) = 1 - 0 = 1.
example : Nat.choose 4 4 - Nat.choose 4 5 = 1 := by native_decide

-- m=5, n=1: C(6,5) - C(6,6) = 6 - 1 = 5.
example : Nat.choose 6 5 - Nat.choose 6 6 = 5 := by native_decide

-- m=5, n=3: C(8,5) - C(8,6) = 56 - 28 = 28.
example : Nat.choose 8 5 - Nat.choose 8 6 = 28 := by native_decide

/-! ## 2. Ballot Sequences (Cycle Lemma)

Out of all arrangements of m copies of +1 and n copies of -1 (m > n),
exactly (m-n)/(m+n) of the C(m+n,m) sequences have all partial sums > 0.

Formula: (m-n) * C(m+n, m) / (m+n).
-/

-- m=3, n=2: 1 * C(5,3) / 5 = 10/5 = 2
example : 1 * Nat.choose 5 3 / 5 = 2 := by native_decide

-- m=4, n=2: 2 * C(6,4) / 6 = 30/6 = 5
example : 2 * Nat.choose 6 4 / 6 = 5 := by native_decide

-- m=4, n=1: 3 * C(5,4) / 5 = 15/5 = 3
example : 3 * Nat.choose 5 4 / 5 = 3 := by native_decide

-- m=5, n=1: 4 * C(6,5) / 6 = 24/6 = 4
example : 4 * Nat.choose 6 5 / 6 = 4 := by native_decide

-- m=5, n=2: 3 * C(7,5) / 7 = 63/7 = 9
example : 3 * Nat.choose 7 5 / 7 = 9 := by native_decide

-- m=6, n=2: 4 * C(8,6) / 8 = 112/8 = 14
example : 4 * Nat.choose 8 6 / 8 = 14 := by native_decide

/-! ## 3. Dyck Paths and Narayana Numbers

Dyck paths of length 2n are counted by Catalan(n).
The Narayana number N(n,k) counts Dyck paths of length 2n with exactly k peaks:
  N(n,k) = (1/n) * C(n,k) * C(n,k-1).

The sum of N(n,k) over k=1..n equals Catalan(n).
-/

/-- Narayana number N(n,k) = (1/n) * C(n,k) * C(n,k-1), with N(0,0)=1. -/
def narayana (n k : ℕ) : ℕ :=
  if n = 0 then (if k = 0 then 1 else 0)
  else if k = 0 then 0
  else Nat.choose n k * Nat.choose n (k - 1) / n

-- Row n=1: N(1,1) = 1
example : narayana 1 1 = 1 := by native_decide

-- Row n=2: N(2,1)=1, N(2,2)=1; sum = 2 = Catalan(2)
example : narayana 2 1 = 1 := by native_decide
example : narayana 2 2 = 1 := by native_decide
example : narayana 2 1 + narayana 2 2 = 2 := by native_decide

-- Row n=3: N(3,1)=1, N(3,2)=3, N(3,3)=1; sum = 5 = Catalan(3)
example : narayana 3 1 = 1 := by native_decide
example : narayana 3 2 = 3 := by native_decide
example : narayana 3 3 = 1 := by native_decide
example : narayana 3 1 + narayana 3 2 + narayana 3 3 = 5 := by native_decide

-- Row n=4: N(4,1)=1, N(4,2)=6, N(4,3)=6, N(4,4)=1; sum = 14 = Catalan(4)
example : narayana 4 1 = 1 := by native_decide
example : narayana 4 2 = 6 := by native_decide
example : narayana 4 3 = 6 := by native_decide
example : narayana 4 4 = 1 := by native_decide
example : narayana 4 1 + narayana 4 2 + narayana 4 3 + narayana 4 4 = 14 := by native_decide

-- Row n=5: N(5,1)=1, N(5,2)=10, N(5,3)=20, N(5,4)=10, N(5,5)=1; sum = 42 = Catalan(5)
example : narayana 5 1 = 1 := by native_decide
example : narayana 5 2 = 10 := by native_decide
example : narayana 5 3 = 20 := by native_decide
example : narayana 5 4 = 10 := by native_decide
example : narayana 5 5 = 1 := by native_decide
example : narayana 5 1 + narayana 5 2 + narayana 5 3 + narayana 5 4 + narayana 5 5 = 42 :=
  by native_decide

/-! ## 4. Motzkin Paths

A Motzkin path of length n uses steps U=(+1), D=(-1), H=(0) and stays ≥ 0.
Motzkin numbers: M_0=1, M_1=1, M_2=2, M_3=4, M_4=9, M_5=21, M_6=51, M_7=127.

The alternative formula via Catalan numbers:
  M_n = Σ_{k=0}^{⌊n/2⌋} C(n, 2k) * Catalan(k).
-/

/-- Catalan number C_k = C(2k,k)/(k+1). -/
def catalan (k : ℕ) : ℕ := Nat.choose (2 * k) k / (k + 1)

/-- Motzkin number via Catalan sum formula. -/
def motzkin (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * k) * catalan k

-- Verify Motzkin table
example : motzkin 0 = 1 := by native_decide
example : motzkin 1 = 1 := by native_decide
example : motzkin 2 = 2 := by native_decide
example : motzkin 3 = 4 := by native_decide
example : motzkin 4 = 9 := by native_decide
example : motzkin 5 = 21 := by native_decide
example : motzkin 6 = 51 := by native_decide
example : motzkin 7 = 127 := by native_decide

-- Motzkin recurrence: (n+3)*M_{n+2} = (2n+5)*M_{n+1} + 3*(n+1)*M_n
-- Equivalently: (n+2)*M_{n+1} = (2n+3)*M_n + 3*n*M_{n-1} for n≥1.
-- Verify at n=2..6 directly from table values.

/-- Motzkin table for recurrence checks. -/
def motzkinTable : Fin 8 → ℕ := ![1, 1, 2, 4, 9, 21, 51, 127]

-- Recurrence: (n+2)*M_{n+1} = (2n+3)*M_n + 3*n*M_{n-1}, for n = 1..5.
-- n=1: 3*M_2 = 5*M_1 + 3*M_0 → 3*2 = 5*1 + 3*1 = 8? No, 6 ≠ 8.
-- The correct recurrence is (n+3)*M_{n+1} = (2n+3)*M_n + 3*n*M_{n-1}.
-- n=1: 4*M_2 = 5*M_1 + 3*M_0 = 5+3 = 8. 4*2=8. ✓
-- n=2: 5*M_3 = 7*M_2 + 6*M_1 = 14+6 = 20. 5*4=20. ✓
-- n=3: 6*M_4 = 9*M_3 + 9*M_2 = 36+18 = 54. 6*9=54. ✓
-- n=4: 7*M_5 = 11*M_4 + 12*M_3 = 99+48 = 147. 7*21=147. ✓
-- n=5: 8*M_6 = 13*M_5 + 15*M_4 = 273+135 = 408. 8*51=408. ✓

example : 4 * motzkinTable 2 = 5 * motzkinTable 1 + 3 * motzkinTable 0 := by native_decide
example : 5 * motzkinTable 3 = 7 * motzkinTable 2 + 6 * motzkinTable 1 := by native_decide
example : 6 * motzkinTable 4 = 9 * motzkinTable 3 + 9 * motzkinTable 2 := by native_decide
example : 7 * motzkinTable 5 = 11 * motzkinTable 4 + 12 * motzkinTable 3 := by native_decide
example : 8 * motzkinTable 6 = 13 * motzkinTable 5 + 15 * motzkinTable 4 := by native_decide

/-! ## 5. Schröder Paths

Large Schröder numbers r_n count paths from (0,0) to (n,n) using steps (1,0),(0,1),(1,1)
that never go above the diagonal (equivalently, lattice paths with long steps).

r_0=1, r_1=2, r_2=6, r_3=22, r_4=90, r_5=394, r_6=1806.

Recurrence: (n+1)*r_n = (6n-3)*r_{n-1} - (n-2)*r_{n-2} for n ≥ 2.
-/

/-- Large Schröder number table. -/
def schroederTable : Fin 7 → ℕ := ![1, 2, 6, 22, 90, 394, 1806]

-- n=2: 3*r_2 = 9*r_1 - 0*r_0 = 18 - 0 = 18. 3*6=18. ✓
example : 3 * schroederTable 2 = 9 * schroederTable 1 - 0 * schroederTable 0 := by native_decide

-- n=3: 4*r_3 = 15*r_2 - 1*r_1 = 90 - 2 = 88. 4*22=88. ✓
example : 4 * schroederTable 3 = 15 * schroederTable 2 - 1 * schroederTable 1 := by native_decide

-- n=4: 5*r_4 = 21*r_3 - 2*r_2 = 462 - 12 = 450. 5*90=450. ✓
example : 5 * schroederTable 4 = 21 * schroederTable 3 - 2 * schroederTable 2 := by native_decide

-- n=5: 6*r_5 = 27*r_4 - 3*r_3 = 2430 - 66 = 2364. 6*394=2364. ✓
example : 6 * schroederTable 5 = 27 * schroederTable 4 - 3 * schroederTable 3 := by native_decide

-- n=6: 7*r_6 = 33*r_5 - 4*r_4 = 13002 - 360 = 12642. 7*1806=12642. ✓
example : 7 * schroederTable 6 = 33 * schroederTable 5 - 4 * schroederTable 4 := by native_decide

-- Little Schröder numbers s_n = r_n / 2 for n ≥ 1; s_0 = 1.
-- s: 1, 1, 3, 11, 45, 197, 903.
example : schroederTable 1 / 2 = 1 := by native_decide
example : schroederTable 2 / 2 = 3 := by native_decide
example : schroederTable 3 / 2 = 11 := by native_decide
example : schroederTable 4 / 2 = 45 := by native_decide
example : schroederTable 5 / 2 = 197 := by native_decide
example : schroederTable 6 / 2 = 903 := by native_decide

/-! ## 6. Central Trinomial Coefficients

The central trinomial coefficient T_n = [x^n](1 + x + x^2)^n counts lattice paths
of length n using steps {-1, 0, +1} that return to 0.

Formula: T_n = Σ_{j=0}^{⌊n/2⌋} C(n, 2j) * C(2j, j).

Table: T_0=1, T_1=1, T_2=3, T_3=7, T_4=19, T_5=51, T_6=141, T_7=393.
-/

/-- Central trinomial coefficient. -/
def centralTrinomial (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * j) * Nat.choose (2 * j) j

example : centralTrinomial 0 = 1 := by native_decide
example : centralTrinomial 1 = 1 := by native_decide
example : centralTrinomial 2 = 3 := by native_decide
example : centralTrinomial 3 = 7 := by native_decide
example : centralTrinomial 4 = 19 := by native_decide
example : centralTrinomial 5 = 51 := by native_decide
example : centralTrinomial 6 = 141 := by native_decide
example : centralTrinomial 7 = 393 := by native_decide

-- Note: T_6 = M_6 = 51 (same for n=5,6 by coincidence of Motzkin and trinomial).
-- Actually T_5 = 51 = M_6, and M_5 = 21 ≠ T_5. Let's just check a cross-reference:
-- T_6 = 141, M_7 = 127, distinct as expected.

-- Trinomial recurrence: (n+1)*T_{n+1} = (2n+1)*T_n + 3*n*T_{n-1}.
-- n=1: 2*T_2 = 3*T_1 + 3*T_0 = 3+3 = 6. 2*3=6. ✓
example : 2 * centralTrinomial 2 = 3 * centralTrinomial 1 + 3 * centralTrinomial 0 :=
  by native_decide

-- n=2: 3*T_3 = 5*T_2 + 6*T_1 = 15+6 = 21. 3*7=21. ✓
example : 3 * centralTrinomial 3 = 5 * centralTrinomial 2 + 6 * centralTrinomial 1 :=
  by native_decide

-- n=3: 4*T_4 = 7*T_3 + 9*T_2 = 49+27 = 76. 4*19=76. ✓
example : 4 * centralTrinomial 4 = 7 * centralTrinomial 3 + 9 * centralTrinomial 2 :=
  by native_decide

-- n=4: 5*T_5 = 9*T_4 + 12*T_3 = 171+84 = 255. 5*51=255. ✓
example : 5 * centralTrinomial 5 = 9 * centralTrinomial 4 + 12 * centralTrinomial 3 :=
  by native_decide

-- n=5: 6*T_6 = 11*T_5 + 15*T_4 = 561+285 = 846. 6*141=846. ✓
example : 6 * centralTrinomial 6 = 11 * centralTrinomial 5 + 15 * centralTrinomial 4 :=
  by native_decide

/-! ## 7. Cross-checks

Linking the sequences to each other and to Catalan numbers. -/

-- Motzkin M_n = centralTrinomial n for no n > 2 in general;
-- but verify a few explicit values are distinct.
example : motzkin 4 = 9 := by native_decide
example : centralTrinomial 4 = 19 := by native_decide

-- Catalan from Narayana row sums (redundant but cross-checks narayana def):
-- Catalan(3) = Σ N(3,k) = 1+3+1 = 5
example : ∑ k ∈ Finset.range 4, narayana 3 k = 5 := by native_decide

-- Catalan(4) = Σ N(4,k) = 1+6+6+1 = 14
example : ∑ k ∈ Finset.range 5, narayana 4 k = 14 := by native_decide

-- Catalan(5) = Σ N(5,k) = 42
example : ∑ k ∈ Finset.range 6, narayana 5 k = 42 := by native_decide

-- Catalan(6) = 132; verify via formula
example : catalan 6 = 132 := by native_decide

-- Schröder and Catalan: r_n = Σ_{k=0}^{n} N(n,k) * 2^{n-k}  (Eu-Liu identity).
-- Spot-check n=3: Σ N(3,k)*2^{3-k} = 1*4 + 3*2 + 1*1 = 4+6+1 = 11.
-- But r_3 = 22, so this counts something else. Use n=3 large Schröder as 22.
-- The identity Σ_k N(n,k)*2^k = r_n (large Schröder).
-- n=3: N(3,1)*2 + N(3,2)*4 + N(3,3)*8 = 2+12+8 = 22. ✓
example : narayana 3 1 * 2 + narayana 3 2 * 4 + narayana 3 3 * 8 =
    schroederTable 3 := by native_decide

-- n=4: N(4,k)*2^k sum = 1*2+6*4+6*8+1*16 = 2+24+48+16 = 90. ✓
example : narayana 4 1 * 2 + narayana 4 2 * 4 + narayana 4 3 * 8 + narayana 4 4 * 16 =
    schroederTable 4 := by native_decide

end WalksCounting
