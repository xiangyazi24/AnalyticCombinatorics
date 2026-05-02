import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace GraphEnumeration

/-! # Graph Enumeration

Basic counting results for labelled graphs: edge-count distribution,
handshaking lemma, chromatic polynomial of complete graphs, Euler's formula,
and total graph count.
-/

-- §1. Labelled graphs edge-count distribution
-- Number of graphs on n vertices with exactly m edges = C(C(n,2), m).

/-- Number of labelled graphs on `n` vertices with exactly `m` edges. -/
def graphsByEdges (n m : ℕ) : ℕ := Nat.choose (Nat.choose n 2) m

example : graphsByEdges 4 0 = 1 := by native_decide
example : graphsByEdges 4 1 = 6 := by native_decide
example : graphsByEdges 4 2 = 15 := by native_decide
example : graphsByEdges 4 3 = 20 := by native_decide
example : graphsByEdges 4 6 = 1 := by native_decide
example : graphsByEdges 3 0 = 1 := by native_decide
example : graphsByEdges 3 3 = 1 := by native_decide

-- §2. Handshaking lemma
-- Sum of degrees = 2 * edges. For complete graph K_n: n*(n-1) = 2*C(n,2).

example : 4 * 3 = 2 * Nat.choose 4 2 := by native_decide
example : 5 * 4 = 2 * Nat.choose 5 2 := by native_decide
example : 10 * 9 = 2 * Nat.choose 10 2 := by native_decide

-- §3. Chromatic polynomial of complete graph
-- χ(K_n, k) = k*(k-1)*...*(k-n+1) = falling factorial.

/-- Chromatic polynomial of the complete graph K_n evaluated at k colors. -/
def chromaticKn (n k : ℕ) : ℕ := ∏ i ∈ Finset.range n, (k - i)

example : chromaticKn 3 3 = 6 := by native_decide
example : chromaticKn 3 4 = 24 := by native_decide
example : chromaticKn 4 4 = 24 := by native_decide

-- §4. Cross-verify: chromaticKn n n = n!

example : chromaticKn 4 4 = Nat.factorial 4 := by native_decide
example : chromaticKn 5 5 = Nat.factorial 5 := by native_decide
example : chromaticKn 6 6 = Nat.factorial 6 := by native_decide

-- §5. Euler's formula for planar graphs: V - E + F = 2.
-- Rearranged as V + F = E + 2 to avoid natural number subtraction issues.

/-- K_4: V=4, E=6, F=4. -/
example : 4 + 4 = 6 + 2 := by native_decide

/-- Cube: V=8, E=12, F=6. -/
example : 8 + 6 = 12 + 2 := by native_decide

/-- Octahedron: V=6, E=12, F=8. -/
example : 6 + 8 = 12 + 2 := by native_decide

-- §6. Total labelled graphs on n vertices = 2^C(n,2).

/-- Total number of labelled graphs on `n` vertices. -/
def totalGraphs (n : ℕ) : ℕ := 2 ^ (Nat.choose n 2)

example : totalGraphs 1 = 1 := by native_decide
example : totalGraphs 2 = 2 := by native_decide
example : totalGraphs 3 = 8 := by native_decide
example : totalGraphs 4 = 64 := by native_decide

end GraphEnumeration
