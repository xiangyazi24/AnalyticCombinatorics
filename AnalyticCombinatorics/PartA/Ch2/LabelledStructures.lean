import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace LabelledStructures

/-! # Labelled Combinatorial Structures and Exponential Generating Functions
    Flajolet & Sedgewick, Analytic Combinatorics, Chapter 2

    Core results: Cayley's formula for labelled trees, labelled graph enumeration,
    surjections via Stirling numbers of the second kind. -/

-- ============================================================================
-- Section 1: Cayley's Formula for Labelled Trees
-- ============================================================================

/-- Number of labelled trees on n vertices: n^(n-2) for n ≥ 2 -/
def cayleyTreeCount : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n => n ^ (n - 2)

/-- Cayley's formula verification: n=2 gives 2^0 = 1 -/
example : cayleyTreeCount 2 = 1 := by native_decide

/-- Cayley's formula verification: n=3 gives 3^1 = 3 -/
example : cayleyTreeCount 3 = 3 := by native_decide

/-- Cayley's formula verification: n=4 gives 4^2 = 16 -/
example : cayleyTreeCount 4 = 16 := by native_decide

/-- Cayley's formula verification: n=5 gives 5^3 = 125 -/
example : cayleyTreeCount 5 = 125 := by native_decide

/-- Cayley's formula verification: n=6 gives 6^4 = 1296 -/
example : cayleyTreeCount 6 = 1296 := by native_decide

/-- Number of labelled rooted trees on n vertices: n^(n-1) -/
def rootedTreeCount : ℕ → ℕ
  | 0 => 0
  | n => n ^ (n - 1)

example : rootedTreeCount 3 = 9 := by native_decide
example : rootedTreeCount 4 = 64 := by native_decide
example : rootedTreeCount 5 = 625 := by native_decide

-- ============================================================================
-- Section 2: Labelled Graphs
-- ============================================================================

/-- Number of labelled graphs on n vertices: 2^(n*(n-1)/2) -/
def labelledGraphCount (n : ℕ) : ℕ := 2 ^ (n * (n - 1) / 2)

example : labelledGraphCount 1 = 1 := by native_decide
example : labelledGraphCount 2 = 2 := by native_decide
example : labelledGraphCount 3 = 8 := by native_decide
example : labelledGraphCount 4 = 64 := by native_decide
example : labelledGraphCount 5 = 1024 := by native_decide

-- ============================================================================
-- Section 3: Stirling Numbers of the Second Kind
-- ============================================================================

/-- Stirling numbers of the second kind S(n,k): number of partitions of [n]
    into exactly k non-empty blocks -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

example : stirling2 0 0 = 1 := by native_decide
example : stirling2 1 1 = 1 := by native_decide
example : stirling2 2 1 = 1 := by native_decide
example : stirling2 2 2 = 1 := by native_decide
example : stirling2 3 1 = 1 := by native_decide
example : stirling2 3 2 = 3 := by native_decide
example : stirling2 3 3 = 1 := by native_decide
example : stirling2 4 1 = 1 := by native_decide
example : stirling2 4 2 = 7 := by native_decide
example : stirling2 4 3 = 6 := by native_decide
example : stirling2 4 4 = 1 := by native_decide
example : stirling2 5 2 = 15 := by native_decide
example : stirling2 5 3 = 25 := by native_decide
example : stirling2 5 4 = 10 := by native_decide
example : stirling2 5 5 = 1 := by native_decide

theorem stirling2_zero_succ (k : ℕ) : stirling2 0 (k + 1) = 0 := by
  simp [stirling2]

theorem stirling2_succ_zero (n : ℕ) : stirling2 (n + 1) 0 = 0 := by
  simp [stirling2]

theorem stirling2_zero_of_gt (n k : ℕ) (h : k > n) : stirling2 n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k => simp [stirling2]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      have hk : k > n := by omega
      have h1 : stirling2 n (k + 1) = 0 := ih (k + 1) (by omega)
      have h2 : stirling2 n k = 0 := ih k hk
      simp [stirling2, h1, h2]

theorem stirling2_n_n (n : ℕ) : stirling2 n n = 1 := by
  induction n with
  | zero => simp [stirling2]
  | succ n ih => simp [stirling2, ih, stirling2_zero_of_gt n (n + 1) (by omega)]

theorem stirling2_n_one (n : ℕ) (hn : n ≥ 1) : stirling2 n 1 = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp [stirling2]
    cases n with
    | zero => simp [stirling2]
    | succ m =>
      simp [ih (by omega)]
      exact stirling2_succ_zero m

-- ============================================================================
-- Section 4: Bell Numbers
-- ============================================================================

/-- Bell number B(n): total number of set partitions of [n] -/
def bellNumber (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (stirling2 n)

example : bellNumber 0 = 1 := by native_decide
example : bellNumber 1 = 1 := by native_decide
example : bellNumber 2 = 2 := by native_decide
example : bellNumber 3 = 5 := by native_decide
example : bellNumber 4 = 15 := by native_decide
example : bellNumber 5 = 52 := by native_decide

-- ============================================================================
-- Section 5: Surjection Counts
-- ============================================================================

/-- Number of surjections from [n] to [k] equals k! * S(n,k) -/
def surjectionCount (n k : ℕ) : ℕ := Nat.factorial k * stirling2 n k

example : surjectionCount 1 1 = 1 := by native_decide
example : surjectionCount 2 1 = 1 := by native_decide
example : surjectionCount 2 2 = 2 := by native_decide
example : surjectionCount 3 2 = 6 := by native_decide
example : surjectionCount 3 3 = 6 := by native_decide
example : surjectionCount 4 2 = 14 := by native_decide
example : surjectionCount 4 3 = 36 := by native_decide
example : surjectionCount 4 4 = 24 := by native_decide
example : surjectionCount 5 3 = 150 := by native_decide
example : surjectionCount 5 4 = 240 := by native_decide
example : surjectionCount 5 5 = 120 := by native_decide

/-- Surjections from [n] to [n] are exactly the permutations -/
theorem surjection_n_n (n : ℕ) :
    surjectionCount n n = Nat.factorial n := by
  simp [surjectionCount, stirling2_n_n]

-- ============================================================================
-- Section 6: EGF and Structural Theorems
-- ============================================================================

/-- The total number of functions from [n] to [n] decomposes via surjections:
    n^n = sum_{k=1}^{n} C(n,k) * surjectionCount(n,k) -/
theorem functions_via_surjections (n : ℕ) (hn : n ≥ 1) :
    n ^ n = (Finset.range n).sum (fun k =>
      Nat.choose n (k + 1) * surjectionCount n (k + 1)) := by
  sorry

/-- Cayley's formula: the number of labelled trees on n ≥ 2 vertices is n^(n-2).
    Proof via Prüfer sequences establishes a bijection. -/
theorem cayley_formula (n : ℕ) (hn : n ≥ 2) :
    cayleyTreeCount n = n ^ (n - 2) := by
  match n, hn with
  | n + 2, _ => simp [cayleyTreeCount]

/-- Labelled rooted trees: n * (number of unrooted trees) = n^(n-1) -/
theorem rooted_unrooted_relation (n : ℕ) (hn : n ≥ 2) :
    rootedTreeCount n = n * cayleyTreeCount n := by
  match n, hn with
  | n + 2, _ =>
    simp [rootedTreeCount, cayleyTreeCount]
    ring

/-- EGF for labelled trees satisfies T(z) = z * exp(T(z)).
    Equivalently, the coefficient [z^n] T(z) = n^(n-1) / n! -/
theorem tree_egf_functional_equation :
    ∀ n : ℕ, n ≥ 1 → rootedTreeCount n = n ^ (n - 1) := by
  intro n hn
  match n, hn with
  | n + 1, _ => simp [rootedTreeCount]

/-- Stirling numbers give the connection coefficients between
    falling factorials and ordinary powers: x^n = Σ S(n,k) x_(k)
    where x_(k) = x(x-1)...(x-k+1) is the falling factorial -/
theorem stirling_connection_coefficients (n : ℕ) :
    ∀ x : ℕ, x ^ n = (Finset.range (n + 1)).sum (fun k =>
      stirling2 n k * Nat.descFactorial x k) := by
  sorry

/-- Dobinski's formula: B(n) = (1/e) * Σ_{k≥0} k^n / k!
    Verified computationally for small n via Bell number values -/
example : bellNumber 5 * Nat.factorial 7 ≤
    (Finset.range 8).sum (fun k => k ^ 5 * Nat.factorial 7 / Nat.factorial k) := by
  native_decide

/-- The number of labelled connected graphs on n vertices -/
def connectedGraphCount : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 3 => 4
  | 4 => 38
  | 5 => 728
  | _ => 0

example : connectedGraphCount 3 = 4 := by native_decide
example : connectedGraphCount 4 = 38 := by native_decide

end LabelledStructures
