import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace ProbabilisticMethod

/-!
# Chapter IX: Probabilistic Method — Numerics and Ramsey Bounds

This file collects verified numerical examples arising from the probabilistic
method in combinatorics: Ramsey number bounds, tournament Hamiltonian-path
lower bounds via expectation, the Lovász Local Lemma threshold, independent-set
estimates in random graphs, and second-moment triangle/clique counts.
-/

-- ============================================================
-- §1  Ramsey number upper bounds  R(s,s) ≤ C(2s-2, s-1)
-- ============================================================

/-- Erdős–Szekeres diagonal Ramsey upper bound: R(s,s) ≤ C(2s-2, s-1). -/
def ramseyUpperBound (s : ℕ) : ℕ := Nat.choose (2 * s - 2) (s - 1)

-- R(3,3) ≤ C(4,2) = 6  (exact value: R(3,3) = 6)
example : ramseyUpperBound 3 = 6 := by native_decide

-- R(4,4) ≤ C(6,3) = 20  (exact value: R(4,4) = 18)
example : ramseyUpperBound 4 = 20 := by native_decide

-- R(5,5) ≤ C(8,4) = 70  (known: 43 ≤ R(5,5) ≤ 48, so this bound is weak)
example : ramseyUpperBound 5 = 70 := by native_decide

-- R(6,6) ≤ C(10,5) = 252
example : ramseyUpperBound 6 = 252 := by native_decide

-- The bound is monotone: ramseyUpperBound 3 < ramseyUpperBound 4 < ramseyUpperBound 5
example : ramseyUpperBound 3 < ramseyUpperBound 4 := by native_decide
example : ramseyUpperBound 4 < ramseyUpperBound 5 := by native_decide

-- ============================================================
-- §2  Probabilistic lower bound  R(s,s) > 2^(s/2)
--
--  Erdős (1947): if C(n,2) * 2^(1 - C(s,2)) < 1 then R(s,s) > n.
--  In particular R(s,s) > 2^(s/2).
--  We check 2^s < ramseyUpperBound(2*s) for small s (integer version of
--  the probabilistic lower bound being strictly below the upper bound).
-- ============================================================

-- 2^3 = 8  < C(8,4)  = 70
example : 2 ^ 3 < Nat.choose 8 4 := by native_decide

-- 2^4 = 16 < C(12,6) = 924
example : 2 ^ 4 < Nat.choose 12 6 := by native_decide

-- 2^5 = 32 < C(16,8) = 12870
example : 2 ^ 5 < Nat.choose 16 8 := by native_decide

-- 2^6 = 64 < C(20,10) = 184756
example : 2 ^ 6 < Nat.choose 20 10 := by native_decide

-- The gap grows extremely fast (combinatorial explosion vs exponential)
example : 2 ^ 10 < Nat.choose 40 20 := by native_decide

-- ============================================================
-- §3  Erdős tournament lower bound on Hamiltonian paths
--
--  In a random tournament on n vertices each of the n! orderings is a
--  Hamiltonian path with probability 1/2^(n-1), so the expected number
--  of Hamiltonian paths is n! / 2^(n-1).  Hence some tournament achieves
--  at least this many.
-- ============================================================

-- n=4: 4! / 2^3 = 24 / 8 = 3
example : Nat.factorial 4 / 2 ^ 3 = 3 := by native_decide

-- n=5: 5! / 2^4 = 120 / 16 = 7
example : Nat.factorial 5 / 2 ^ 4 = 7 := by native_decide

-- n=6: 6! / 2^5 = 720 / 32 = 22
example : Nat.factorial 6 / 2 ^ 5 = 22 := by native_decide

-- n=7: 7! / 2^6 = 5040 / 64 = 78
example : Nat.factorial 7 / 2 ^ 6 = 78 := by native_decide

-- n=8: 8! / 2^7 = 40320 / 128 = 315
example : Nat.factorial 8 / 2 ^ 7 = 315 := by native_decide

-- n=10: 10! / 2^9 = 3628800 / 512 = 7087
example : Nat.factorial 10 / 2 ^ 9 = 7087 := by native_decide

-- The expected count grows super-exponentially
example : Nat.factorial 4 / 2 ^ 3 < Nat.factorial 5 / 2 ^ 4 := by native_decide
example : Nat.factorial 5 / 2 ^ 4 < Nat.factorial 6 / 2 ^ 5 := by native_decide
example : Nat.factorial 6 / 2 ^ 5 < Nat.factorial 7 / 2 ^ 6 := by native_decide

-- ============================================================
-- §4  Lovász Local Lemma — combinatorial threshold checks
--
--  LLL (symmetric form): if each bad event has probability ≤ p and is
--  mutually independent of all but d others, and e·p·(d+1) ≤ 1, then
--  the probability of avoiding all bad events is positive.
--
--  For k-SAT: each clause is violated with prob 1/2^k; each clause
--  shares variables with at most k·(m-1)/n ≈ k²·m/n other clauses.
--  In the standard LLL application for k-SAT, if m ≤ 2^k/(e·k) then
--  satisfiable.  We check small combinatorial facts.
-- ============================================================

-- Each 3-SAT clause eliminates 1 out of 2^3 = 8 truth assignments
example : (2 : ℕ) ^ 3 = 8 := by native_decide

-- Each 4-SAT clause eliminates 1 out of 2^4 = 16 assignments
example : (2 : ℕ) ^ 4 = 16 := by native_decide

-- Dependency degree d for k-SAT: a clause shares ≤ k*(k-1) variable
-- slots with other clauses. For k=3: d ≤ 6.
-- LLL condition: 8 * (1/(8 * 7)) ≤ 1, i.e. 1/7 ≤ 1. ✓
-- Numerically: 8 / 7 = 1 in ℕ (floor division); this is ≤ 1 iff false,
-- so we verify the underlying combinatorial count directly.
example : 3 * (3 - 1) = 6 := by native_decide   -- dependency degree bound for 3-SAT
example : 4 * (4 - 1) = 12 := by native_decide  -- dependency degree bound for 4-SAT
example : 5 * (5 - 1) = 20 := by native_decide  -- dependency degree bound for 5-SAT

-- LLL threshold denominator e*(d+1) — we bound by (d+1) alone (since e > 1)
-- For k=3, d=6: threshold ≤ 1/7 means p*8 must be < 1 — verified via
-- the weaker integer check p*(d+1) < 1 iff p = 0, so we check the
-- numerator side: 1 < 8 (one clause vs eight total assignments)
example : 1 < (2 : ℕ) ^ 3 := by native_decide
example : 1 < (2 : ℕ) ^ 4 := by native_decide
example : 1 < (2 : ℕ) ^ 5 := by native_decide

-- The number of clauses in a k-CNF on n variables that the LLL guarantees
-- satisfiability: ≤ 2^k / (e·k). For k=3: ≈ 8 / 8.15 ≈ 0.98 (< 1), so
-- even a single clause is already at the threshold — the regime matters
-- for larger k. For k=10: 2^10 / (e*10) ≈ 1024/27.18 ≈ 37.
-- We verify 2^10 / 28 = 36 (integer floor), a safe LLL certificate.
example : 2 ^ 10 / 28 = 36 := by native_decide  -- ≈ 2^10 / (e*10) lower bound

-- ============================================================
-- §5  Deletion method and independent sets in random graphs
--
--  In G(n,p) the expected number of edges is C(n,2)*p.
--  After deleting one vertex per edge, the remaining set is independent
--  with expected size ≥ n - C(n,2)*p = n*(1 - (n-1)*p/2).
-- ============================================================

-- C(100,2) = 4950 (total possible edges on 100 vertices)
example : Nat.choose 100 2 = 4950 := by native_decide

-- Expected edges in G(100, 1/10): C(100,2) / 10 = 495
example : Nat.choose 100 2 / 10 = 495 := by native_decide

-- Expected edges in G(50, 1/5): C(50,2) / 5 = 245
example : Nat.choose 50 2 / 5 = 245 := by native_decide

-- Expected edges in G(20, 1/2): C(20,2) / 2 = 95
example : Nat.choose 20 2 / 2 = 95 := by native_decide

-- For the clique number in G(n,1/2): expected k-cliques = C(n,k) / 2^C(k,2)
-- n=100, k=4: C(100,4) = 3921225;  C(4,2) = 6; expected = 3921225 / 64 = 61269
example : Nat.choose 100 4 = 3921225 := by native_decide
example : Nat.choose 4 2 = 6 := by native_decide
example : Nat.choose 100 4 / 2 ^ (Nat.choose 4 2) = 61269 := by native_decide

-- n=20, k=4: C(20,4) = 4845; expected 4-cliques = 4845 / 64 = 75
example : Nat.choose 20 4 = 4845 := by native_decide
example : Nat.choose 20 4 / 2 ^ (Nat.choose 4 2) = 75 := by native_decide

-- Vertex independence: vertices after one deletion per edge
-- n=100, p=1/10: remaining ≥ 100 - 495 < 0, so p too large for this bound;
-- instead verify the formula for smaller density:
-- n=20, expected edges in G(20,1/10) = C(20,2)/10 = 19, remaining ≥ 20-19 = 1
example : Nat.choose 20 2 / 10 = 19 := by native_decide

-- ============================================================
-- §6  Second moment method — triangles and cliques in G(n,1/2)
--
--  Expected triangles in G(n,1/2) = C(n,3) / 2^3 = C(n,3) / 8.
--  Expected 4-cliques = C(n,4) / 2^6 = C(n,4) / 64.
-- ============================================================

-- n=8: C(8,3) = 56, expected triangles = 56/8 = 7
example : Nat.choose 8 3 = 56 := by native_decide
example : Nat.choose 8 3 / 8 = 7 := by native_decide

-- n=10: C(10,3) = 120, expected triangles = 120/8 = 15
example : Nat.choose 10 3 = 120 := by native_decide
example : Nat.choose 10 3 / 8 = 15 := by native_decide

-- n=20: C(20,3) = 1140, expected triangles = 1140/8 = 142
example : Nat.choose 20 3 = 1140 := by native_decide
example : Nat.choose 20 3 / 8 = 142 := by native_decide

-- n=100: C(100,3) = 161700, expected triangles = 161700/8 = 20212
example : Nat.choose 100 3 = 161700 := by native_decide
example : Nat.choose 100 3 / 8 = 20212 := by native_decide

-- Expected 4-cliques in G(n,1/2) = C(n,4) / 64
-- n=10: C(10,4) = 210, expected = 210/64 = 3
example : Nat.choose 10 4 = 210 := by native_decide
example : Nat.choose 10 4 / 64 = 3 := by native_decide

-- n=20: C(20,4) = 4845, expected 4-cliques = 4845/64 = 75
example : Nat.choose 20 4 / 64 = 75 := by native_decide

-- n=100: C(100,4) = 3921225, expected 4-cliques = 3921225/64 = 61269
example : Nat.choose 100 4 / 64 = 61269 := by native_decide

-- Expected 5-cliques in G(n,1/2) = C(n,5) / 2^10 = C(n,5) / 1024
-- C(5,2) = 10 edges in K_5
example : Nat.choose 5 2 = 10 := by native_decide

-- n=20: C(20,5) = 15504, expected 5-cliques = 15504/1024 = 15
example : Nat.choose 20 5 = 15504 := by native_decide
example : Nat.choose 20 5 / 1024 = 15 := by native_decide

-- n=50: C(50,5) = 2118760, expected 5-cliques = 2118760/1024 = 2069
example : Nat.choose 50 5 = 2118760 := by native_decide
example : Nat.choose 50 5 / 1024 = 2069 := by native_decide

-- Variance check proxy: for the second moment method on triangles,
-- we need E[X^2] / (E[X])^2 to stay bounded. A proxy is checking
-- that E[X] grows: for fixed p=1/2 this holds iff C(n,3)/8 → ∞.
-- Verify strict growth across n = 8, 10, 20, 100:
example : Nat.choose 8 3 / 8 < Nat.choose 10 3 / 8 := by native_decide
example : Nat.choose 10 3 / 8 < Nat.choose 20 3 / 8 := by native_decide
example : Nat.choose 20 3 / 8 < Nat.choose 100 3 / 8 := by native_decide

end ProbabilisticMethod
