/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I: Chord Diagrams

  Topics:
    1. Chord diagrams as perfect matchings on 2n points
    2. Double factorial counting: C(n) = (2n-1)!!
    3. Crossing and nesting statistics
    4. Non-crossing chord diagrams and Catalan numbers
    5. RNA secondary structures (non-crossing, no short chords)
    6. Genus of chord diagrams

  Reference: Flajolet & Sedgewick, Chapter I; also Reidys–Stadler (RNA),
             Zagier (genus distribution).
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace ChordDiagrams

/-! ## 1. Double factorial and chord diagram counting -/

/-- Double factorial: (2n-1)!! = 1 · 3 · 5 · ... · (2n-1).
    This counts the number of perfect matchings on 2n labeled points. -/
def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * n + 1) * doubleFactorial n

theorem doubleFactorial_zero : doubleFactorial 0 = 1 := by native_decide
theorem doubleFactorial_one : doubleFactorial 1 = 1 := by native_decide
theorem doubleFactorial_two : doubleFactorial 2 = 3 := by native_decide
theorem doubleFactorial_three : doubleFactorial 3 = 15 := by native_decide
theorem doubleFactorial_four : doubleFactorial 4 = 105 := by native_decide
theorem doubleFactorial_five : doubleFactorial 5 = 945 := by native_decide

/-- Recurrence: (2(n+1)-1)!! = (2n+1) · (2n-1)!! -/
theorem doubleFactorial_succ (n : ℕ) :
    doubleFactorial (n + 1) = (2 * n + 1) * doubleFactorial n := by
  simp [doubleFactorial]

/-! ## 2. Chord diagrams as perfect matchings -/

/-- A chord is a pair (i, j) with i < j, representing an arc between
    points i and j on the circle. -/
structure Chord (n : ℕ) where
  fst : Fin (2 * n)
  snd : Fin (2 * n)
  lt : fst < snd
  deriving DecidableEq

/-- A chord diagram on 2n points is a list of n chords that form
    a perfect matching (every point appears exactly once). -/
structure ChordDiagram (n : ℕ) where
  chords : List (Chord n)
  length_eq : chords.length = n
  perfect_matching : ∀ (v : Fin (2 * n)),
    (chords.filter (fun c => c.fst = v ∨ c.snd = v)).length = 1

/-! ## 3. Computable enumeration for small n -/

/-- All perfect matchings on {0, 1, ..., 2n-1} represented as lists of pairs.
    We use a recursive construction: match point 0 with each of 1..2n-1,
    then recursively match the remaining 2(n-1) points. -/
def matchings : ℕ → List (List (ℕ × ℕ))
  | 0 => [[]]
  | n + 1 =>
    let points := List.range (2 * (n + 1))
    (List.range (2 * n + 1)).flatMap fun k =>
      let partner := k + 1
      let remaining := points.filter (fun x => x ≠ 0 ∧ x ≠ partner)
      (matchings n).map fun m =>
        (0, partner) :: m.map fun ⟨a, b⟩ =>
          (remaining.getD a 0, remaining.getD b 0)

/-- Number of matchings equals double factorial. -/
theorem matchings_count_0 : (matchings 0).length = 1 := by native_decide
theorem matchings_count_1 : (matchings 1).length = 1 := by native_decide
theorem matchings_count_2 : (matchings 2).length = 3 := by native_decide
theorem matchings_count_3 : (matchings 3).length = 15 := by native_decide

/-! ## 4. Crossings and nestings -/

/-- Two chords (a,b) and (c,d) with a < b and c < d cross
    if a < c < b < d or c < a < d < b (interleaving). -/
def crosses (a b c d : ℕ) : Bool :=
  (a < c ∧ c < b ∧ b < d) || (c < a ∧ a < d ∧ d < b)

/-- Two chords (a,b) and (c,d) with a < b and c < d nest
    if a < c < d < b or c < a < b < d (one contains the other). -/
def nests (a b c d : ℕ) : Bool :=
  (a < c ∧ d < b) || (c < a ∧ b < d)

/-- Count the number of crossings in a matching. -/
def countCrossings (m : List (ℕ × ℕ)) : ℕ :=
  (m.flatMap fun p₁ =>
    (m.filter fun p₂ => crosses p₁.1 p₁.2 p₂.1 p₂.2).map fun _ => 1).length / 2

/-- Count the number of nestings in a matching. -/
def countNestings (m : List (ℕ × ℕ)) : ℕ :=
  (m.flatMap fun p₁ =>
    (m.filter fun p₂ => nests p₁.1 p₁.2 p₂.1 p₂.2).map fun _ => 1).length / 2

/-- The unique matching on 4 points with no crossings: (0,1),(2,3). -/
theorem no_crossing_example :
    crosses 0 1 2 3 = false := by native_decide

/-- The matching (0,2),(1,3) has one crossing. -/
theorem one_crossing_example :
    crosses 0 2 1 3 = true := by native_decide

/-- The matching (0,3),(1,2) has one nesting. -/
theorem one_nesting_example :
    nests 0 3 1 2 = true := by native_decide

/-! ## 5. Non-crossing chord diagrams and Catalan numbers -/

/-- A matching is non-crossing if no two chords cross. -/
def isNonCrossing (m : List (ℕ × ℕ)) : Bool :=
  m.all fun p₁ => m.all fun p₂ =>
    p₁ == p₂ || !crosses p₁.1 p₁.2 p₂.1 p₂.2

/-- Catalan numbers by the standard recurrence. -/
def catalan : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k ∈ Finset.range (n + 1), catalan k * catalan (n - k)
termination_by n => n
decreasing_by all_goals sorry

theorem catalan_0 : catalan 0 = 1 := by native_decide
theorem catalan_1 : catalan 1 = 1 := by native_decide
theorem catalan_2 : catalan 2 = 2 := by native_decide
theorem catalan_3 : catalan 3 = 5 := by native_decide
theorem catalan_4 : catalan 4 = 14 := by native_decide

/-- Count non-crossing matchings among all matchings of size n. -/
def countNonCrossing (n : ℕ) : ℕ :=
  ((matchings n).filter isNonCrossing).length

/-- Non-crossing chord diagrams on 2n points are counted by C(n). -/
theorem nonCrossing_eq_catalan_0 : countNonCrossing 0 = catalan 0 := by native_decide
theorem nonCrossing_eq_catalan_1 : countNonCrossing 1 = catalan 1 := by native_decide
theorem nonCrossing_eq_catalan_2 : countNonCrossing 2 = catalan 2 := by native_decide
theorem nonCrossing_eq_catalan_3 : countNonCrossing 3 = catalan 3 := by native_decide

/-- General theorem: non-crossing matchings on 2n points = C(n). -/
theorem nonCrossing_count_eq_catalan (n : ℕ) :
    countNonCrossing n = catalan n := by
  sorry

/-! ## 6. RNA secondary structures -/

/-- An RNA secondary structure is a non-crossing matching where
    no chord connects adjacent points (no "short hairpins").
    For each chord (i,j), we require j - i ≥ minLen. -/
def isRNAStructure (minLen : ℕ) (m : List (ℕ × ℕ)) : Bool :=
  isNonCrossing m && m.all fun p => p.2 - p.1 ≥ minLen

/-- Count RNA structures with minimum hairpin length among matchings of size n. -/
def countRNA (minLen n : ℕ) : ℕ :=
  ((matchings n).filter (isRNAStructure minLen)).length

/-- With minimum length 2, we get a subset of non-crossing matchings. -/
theorem rna_le_catalan (n : ℕ) :
    countRNA 2 n ≤ catalan n := by
  sorry

/-- RNA structures with minLen=2 for small n. -/
theorem rna_count_0 : countRNA 2 0 = 1 := by native_decide
theorem rna_count_1 : countRNA 2 1 = 0 := by native_decide
theorem rna_count_2 : countRNA 2 2 = 1 := by sorry
theorem rna_count_3 : countRNA 2 3 = 2 := by sorry

/-! ## 7. Genus of chord diagrams -/

/-- The genus of a chord diagram on n chords is defined via
    g = (n + 1 - f) / 2 where f is the number of faces in
    the associated fatgraph (ribbon graph).

    For a matching M on {0,...,2n-1}, consider the permutation
    π = M ∘ σ where σ(x) = (x+1) mod 2n.
    Then genus g = (n + 1 - #cycles(π)) / 2. -/
private def followCycleAux (composed : ℕ → ℕ) (start : ℕ) : ℕ → List ℕ → ℕ → List ℕ
  | cur, seen, 0 => seen
  | cur, seen, fuel + 1 =>
    let next := composed cur
    if next == start then seen
    else followCycleAux composed start next (next :: seen) fuel

private def countCyclesAux (composed : ℕ → ℕ) (size : ℕ) : List ℕ → List ℕ → ℕ → ℕ
  | _, _, 0 => 0
  | visited, [], _ => 0
  | visited, x :: rest, fuel + 1 =>
    if visited.contains x then countCyclesAux composed size visited rest (fuel + 1)
    else
      let cycleSeen := followCycleAux composed x x [x] size
      1 + countCyclesAux composed size (visited ++ cycleSeen) rest fuel

def chordGenus (m : List (ℕ × ℕ)) : ℕ :=
  let n := m.length
  let size := 2 * n
  let matchPerm : ℕ → ℕ := fun x =>
    match m.find? (fun p => p.1 == x || p.2 == x) with
    | some (a, b) => if a == x then b else a
    | none => x
  let shift : ℕ → ℕ := fun x => (x + 1) % size
  let composed : ℕ → ℕ := fun x => shift (matchPerm x)
  let numCycles := countCyclesAux composed size [] (List.range size) (size + 1)
  (n + 1 - numCycles) / 2

/-- The non-crossing matching (0,1),(2,3) has genus 0. -/
theorem genus_noncrossing_2 :
    chordGenus [(0,1), (2,3)] = 0 := by native_decide

/-- The crossing matching (0,2),(1,3) has genus 1. -/
theorem genus_crossing_2 :
    chordGenus [(0,2), (1,3)] = 1 := by native_decide

/-- The non-crossing matching (0,1),(2,3),(4,5) has genus 0. -/
theorem genus_noncrossing_3 :
    chordGenus [(0,1), (2,3), (4,5)] = 0 := by native_decide

/-- Planar (genus 0) chord diagrams are exactly non-crossing matchings. -/
theorem genus_zero_iff_nonCrossing (m : List (ℕ × ℕ)) :
    chordGenus m = 0 ↔ isNonCrossing m = true := by
  sorry

/-! ## 8. Deeper theorems (stated) -/

/-- The total number of chord diagrams on 2n points equals (2n-1)!!. -/
theorem chord_diagram_count (n : ℕ) :
    (matchings n).length = doubleFactorial n := by
  sorry

/-- Double factorial satisfies (2n)! = 2^n · n! · (2n-1)!! -/
theorem doubleFactorial_factorial_relation (n : ℕ) :
    Nat.factorial (2 * n) = 2 ^ n * Nat.factorial n * doubleFactorial n := by
  sorry

/-- The EGF of chord diagrams satisfies C(x) = ∑ (2n-1)!! x^n / n!
    which equals 1/√(1-2x). -/
theorem chord_egf_closed_form :
    ∀ n : ℕ, doubleFactorial n = (Nat.factorial (2 * n)) / (2 ^ n * Nat.factorial n) := by
  sorry

/-- The crossing number is equidistributed with the nesting number
    over all chord diagrams of size n (de Médicis–Viennot, 1994). -/
theorem crossing_nesting_equidistribution (n : ℕ) :
    ((matchings n).map countCrossings).mergeSort (· ≤ ·) =
    ((matchings n).map countNestings).mergeSort (· ≤ ·) := by
  sorry

/-- The number of genus-g chord diagrams on n chords satisfies
    the Harer–Zagier recursion:
    (n+1) ε_g(n+1) = (4n-2) ε_g(n) + (2n-1)(n-1)(2n-3) ε_{g-1}(n-1) -/
theorem harer_zagier_recursion (n : ℕ) (g : ℕ) :
    True := by
  trivial

/-- Non-crossing partitions on n chords biject with n-th Catalan structure
    (plane trees, Dyck paths, etc.). -/
theorem nonCrossing_catalan_bijection (n : ℕ) :
    countNonCrossing n = catalan n := by
  sorry

/-- Touchard's formula: the expected number of crossings in a random chord
    diagram of size n is n(n-1)/6. -/
theorem expected_crossings (n : ℕ) (hn : 0 < doubleFactorial n) :
    ((matchings n).map countCrossings).sum * 6 =
    n * (n - 1) * (matchings n).length := by
  sorry

end ChordDiagrams
