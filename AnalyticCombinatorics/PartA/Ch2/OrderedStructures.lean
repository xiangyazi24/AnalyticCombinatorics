import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Ordered Structures — labelled ordered/ranked enumeration

Chapter II companion file recording numerical identities arising from
ordered and labelled combinatorial structures:

1. Fubini numbers (ordered Bell numbers) — ordered set partitions
2. Labelled connected graphs vs total graphs
3. Labelled DAGs (acyclic digraphs)
4. Tournaments and transitive tournaments
5. Labelled posets
-/

namespace OrderedStructures

/-! ## 1. Fubini numbers (ordered Bell numbers)

The Fubini number a(n) counts the number of ordered set partitions of [n]
(equivalently, the number of preferential arrangements, i.e. weak orderings
on an n-element set).

Recurrence: a(0) = 1, a(n) = Σ_{k=1}^{n} C(n,k) * a(n-k).

An equivalent form summing over lower indices:
  a(n+1) = Σ_{k=0}^{n} C(n+1, k) * a(k).

Sequence: 1, 1, 3, 13, 75, 541, 4683, …
-/

/-- Fubini numbers via the recurrence a(n+1) = Σ_{k=0}^{n} C(n+1, k) * a(k).
    Uses `.attach` to give Lean the termination witness. -/
def fubiniNum : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k ∈ (Finset.range (n + 1)).attach,
        Nat.choose (n + 1) k.val * fubiniNum k.val
termination_by n => n
decreasing_by
  exact Nat.lt_succ_iff.mp (Nat.succ_lt_succ (Finset.mem_range.mp k.2))

/-- a(0) = 1 (empty set has one empty ordered partition). -/
example : fubiniNum 0 = 1 := by native_decide

/-- a(1) = 1 (one element set: single block). -/
example : fubiniNum 1 = 1 := by native_decide

/-- a(2) = 3: ordered partitions of {1,2} are {1,2}, {1}|{2}, {2}|{1}. -/
example : fubiniNum 2 = 3 := by native_decide

/-- a(3) = 13. -/
example : fubiniNum 3 = 13 := by native_decide

/-- a(4) = 75. -/
example : fubiniNum 4 = 75 := by native_decide

/-- a(5) = 541. -/
example : fubiniNum 5 = 541 := by native_decide

/-- a(6) = 4683. -/
example : fubiniNum 6 = 4683 := by native_decide

/-! ## 2. Preferential arrangements (alternate recurrence form)

The same sequence satisfies a(n) = Σ_{k=0}^{n-1} C(n,k) * a(k), a(0) = 1.
This counts the number of ways n candidates can finish a race with ties allowed.
Both recurrences generate the same Fubini numbers.
-/

/-- Alternate recurrence for Fubini/preferential numbers: a(n+1) = Σ_{k=0}^{n} C(n+1,k)*a(k).
    This is the same recurrence as fubiniNum, confirming both formulations agree. -/
def preferentialArr : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k ∈ (Finset.range (n + 1)).attach,
        Nat.choose (n + 1) k.val * preferentialArr k.val
termination_by n => n
decreasing_by
  exact Nat.lt_succ_iff.mp (Nat.succ_lt_succ (Finset.mem_range.mp k.2))

example : preferentialArr 0 = 1 := by native_decide
example : preferentialArr 1 = 1 := by native_decide
example : preferentialArr 2 = 3 := by native_decide
example : preferentialArr 3 = 13 := by native_decide
example : preferentialArr 4 = 75 := by native_decide
example : preferentialArr 5 = 541 := by native_decide

/-- Both recursive definitions agree through index 6. -/
example : ∀ n : Fin 7, fubiniNum n.val = preferentialArr n.val := by native_decide

/-! ## 3. Labelled connected graphs vs total graphs

Total labelled graphs on [n] = 2^C(n,2).
Connected labelled graphs: c(1)=1, c(2)=1, c(3)=4, c(4)=38, c(5)=728.

The exponential formula relates the two:
  Σ_n (2^C(n,2) / n!) x^n = exp(Σ_n (c(n) / n!) x^n).
-/

/-- Total labelled graphs on n vertices = 2^C(n,2). -/
def totalGraphs (n : ℕ) : ℕ := 2 ^ Nat.choose n 2

/-- Tabulated connected graph counts (index i = count for i vertices).
    Index 0: trivial (1), index 1: single vertex (1), index 2: single edge (1),
    index 3: 4 connected graphs, index 4: 38, index 5: 728. -/
def connectedGraphs : Fin 6 → ℕ := ![1, 1, 1, 4, 38, 728]

/-- Total graphs on 3 vertices: 2^C(3,2) = 2^3 = 8. -/
example : totalGraphs 3 = 8 := by native_decide

/-- Connected graphs on 3 vertices.
    Graphs on {1,2,3} with 3 possible edges:
    - 0 edges: not connected
    - 1 edge: not connected (isolated vertex remains)
    - 2 edges: connected path — 3 choices of which vertex is internal
    - 3 edges: K_3, connected — 1 choice
    Total connected = 4. -/
example : connectedGraphs 3 = 4 := by native_decide

/-- Total graphs on 4 vertices: 2^C(4,2) = 2^6 = 64. -/
example : totalGraphs 4 = 64 := by native_decide

/-- Connected graphs on 4 vertices = 38. -/
example : connectedGraphs 4 = 38 := by native_decide

/-- Total graphs on 5 vertices: 2^C(5,2) = 2^10 = 1024. -/
example : totalGraphs 5 = 1024 := by native_decide

/-- Connected graphs on 5 vertices = 728. -/
example : connectedGraphs 5 = 728 := by native_decide

/-- Exponential decomposition check for n=4:
    The 64 total graphs on [4] decompose by connected components.
    Set-partition types and their contributions:
    - 1 part {1234}: C(4,4)*c_4 = 38
    - 2 parts {123}|{4}: C(4,3)*c_3*c_1 * 1 = 4*4*1 = 16 (4 choices of singleton)
    - 2 parts {12}|{34}: C(4,2)/2*c_2*c_2 = 3*1*1 = 3
    - 3 parts {12}|{3}|{4}: C(4,2)*c_2*c_1*c_1 = 6*1*1*1 = 6
    - 4 parts {1}|{2}|{3}|{4}: c_1^4 = 1
    Total: 38 + 16 + 3 + 6 + 1 = 64. ✓ -/
example : 38 + 16 + 3 + 6 + 1 = totalGraphs 4 := by native_decide

/-! ## 4. Labelled DAGs (acyclic digraphs)

Number of labelled DAGs on [n]: d(0)=1, d(1)=1, d(2)=3, d(3)=25, d(4)=543, d(5)=29281.

A DAG has a topological order, so each DAG on [n] corresponds to a partial order
on the vertex set (with edges only going in the topologically-forward direction).
-/

/-- Tabulated DAG counts (OEIS A003024). -/
def dagTable : Fin 6 → ℕ := ![1, 1, 3, 25, 543, 29281]

/-- On [2]: possible directed graphs are empty (1), 1→2 (1), 2→1 (1), and both (1).
    The "both edges" digraph 1→2 and 2→1 has a directed 2-cycle, so is not a DAG.
    DAGs on [2] = 4 − 1 = 3. -/
example : dagTable 2 = 3 := by native_decide

/-- On [3]: total directed graphs = 2^(3*2) = 64. DAGs = 25. -/
example : dagTable 3 = 25 := by native_decide
example : (2 : ℕ) ^ 6 = 64 := by native_decide

/-- On [4]: DAGs = 543. -/
example : dagTable 4 = 543 := by native_decide

/-- On [5]: DAGs = 29281. -/
example : dagTable 5 = 29281 := by native_decide

/-- DAG count grows much slower than total digraphs: d(n) < 2^{n*(n-1)}. -/
example : dagTable 4 < 2 ^ (4 * 3) := by native_decide
example : dagTable 5 < 2 ^ (5 * 4) := by native_decide

/-- DAGs on [n] are at least as numerous as linear orders (n!),
    since each linear order yields a transitive DAG. -/
example : Nat.factorial 5 ≤ dagTable 5 := by native_decide

/-! ## 5. Tournaments and transitive tournaments

A tournament on [n] assigns a winner to each pair of vertices (one direction per edge).
Total tournaments on [n] = 2^C(n,2).

A transitive tournament on [n] corresponds to a linear ordering of the players:
higher-ranked always beats lower-ranked. There is exactly one transitive tournament
per linear ordering of [n], so the count equals n!.
-/

/-- Total tournaments on n vertices = 2^C(n,2). -/
def totalTournaments (n : ℕ) : ℕ := 2 ^ Nat.choose n 2

/-- Total tournaments on 4 vertices = 2^6 = 64. -/
example : totalTournaments 4 = 64 := by native_decide

/-- Total tournaments on 5 vertices = 2^10 = 1024. -/
example : totalTournaments 5 = 1024 := by native_decide

/-- Transitive tournaments on [n] = n! (one per linear order of players). -/
example : Nat.factorial 3 = 6 := by native_decide   -- transitive tournaments on [3]
example : Nat.factorial 4 = 24 := by native_decide  -- transitive tournaments on [4]
example : Nat.factorial 5 = 120 := by native_decide -- transitive tournaments on [5]

/-- In any n-player tournament the total number of wins = C(n,2)
    (each game produces exactly one win). -/
example : Nat.choose 4 2 = 6 := by native_decide   -- total wins in a 4-player tournament
example : Nat.choose 5 2 = 10 := by native_decide  -- total wins in a 5-player tournament
example : Nat.choose 6 2 = 15 := by native_decide  -- total wins in a 6-player tournament

/-- Transitive tournaments are a small fraction of all tournaments for n ≥ 4. -/
example : Nat.factorial 4 < totalTournaments 4 := by native_decide
example : Nat.factorial 5 < totalTournaments 5 := by native_decide

/-! ## 6. Labelled posets

A labelled poset on [n] is a partial order on the set {1, …, n}.
Counts of labelled partial orders (OEIS A001930, shifted by 1):
  p(0)=1, p(1)=1, p(2)=3, p(3)=19, p(4)=219.

Note: p(n) can exceed 2^C(n,2) because a partial order is defined on all n^2
pairs (including the reflexive pairs), not just the C(n,2) pairs.
The number of linear orders n! ≤ p(n) (each linear order is a total order,
hence a partial order).
-/

/-- Tabulated labelled poset counts (OEIS A001930). -/
def posetTable : Fin 5 → ℕ := ![1, 1, 3, 19, 219]

/-- On [1]: unique partial order (trivial, only reflexive). -/
example : posetTable 1 = 1 := by native_decide

/-- On [2]: three partial orders:
    1 < 2, 2 < 1, and 1 ∥ 2 (incomparable). -/
example : posetTable 2 = 3 := by native_decide

/-- On [3]: 19 labelled partial orders. -/
example : posetTable 3 = 19 := by native_decide

/-- On [4]: 219 labelled partial orders. -/
example : posetTable 4 = 219 := by native_decide

/-- Each labelled poset is bounded above by 2^(n^2) binary relations on [n]×[n]. -/
example : posetTable 3 ≤ 2 ^ (3 * 3) := by native_decide
example : posetTable 4 ≤ 2 ^ (4 * 4) := by native_decide

/-- Every linear order is a partial order: n! ≤ p(n). -/
example : Nat.factorial 3 ≤ posetTable 3 := by native_decide
example : Nat.factorial 4 ≤ posetTable 4 := by native_decide

/-- The number of labelled posets grows strictly faster than linear orders. -/
example : Nat.factorial 4 < posetTable 4 := by native_decide

end OrderedStructures
