# Task: Maps and Planar Structures (Ch I/VII)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/PlanarMaps.lean`.

## What to formalize

Counting planar maps and related structures.

1. **Rooted planar maps (Tutte's formula):**
   Number of rooted planar maps with n edges:
   M_n = 2 * (2n)! * 3^n / ((n+1)! * (n+2)!)
   ```lean
   def rootedMapCount (n : ℕ) : ℕ :=
     2 * Nat.factorial (2*n) * 3^n / (Nat.factorial (n+1) * Nat.factorial (n+2))
   ```
   Verify: M_0 = 1 (? actually M_0 = 2... let me check)
   
   Actually: M_0 = 1 (vertex map), M_1 = 2, M_2 = 9, M_3 = 54, M_4 = 378.
   
   Use the recurrence instead:
   ```lean
   def rootedMapCount : ℕ → ℕ
     | 0 => 1
     | n + 1 => -- complicated
   ```
   
   Just use a verified table:
   ```lean
   def rootedMapTable : Fin 6 → ℕ
     | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 2 | ⟨2, _⟩ => 9
     | ⟨3, _⟩ => 54 | ⟨4, _⟩ => 378 | ⟨5, _⟩ => 2916
   ```
   Verify using Tutte's formula: M_n = 2*(2n)!*3^n / ((n+1)!*(n+2)!)
   Check: M_1 = 2*2*3/(2*6) = 12/12 = 1? No...
   
   Let me recalculate: M_n = 2·3^n·(2n)!/((n+2)!·(n+1)!)
   n=1: 2·3·2/(6·2) = 12/12 = 1. But M_1 should be 2...
   
   Different formula: rooted maps = Cat(n) * 2 * 3^n ... 
   Actually for planar maps the formula is complex. Use simpler structures.

2. **Triangulations of polygon:**
   Number of triangulations of (n+2)-gon = Catalan(n).
   ```lean
   def triangulationCount (n : ℕ) : ℕ := Nat.choose (2*n) n / (n + 1)
   ```
   Verify: T(1)=1 (triangle), T(2)=2 (square), T(3)=5 (pentagon), T(4)=14 (hexagon)

3. **Dissections of polygon (Schröder):**
   Number of dissections of (n+1)-gon into polygons = little Schröder number s(n).
   s(1)=1, s(2)=1, s(3)=3, s(4)=11, s(5)=45, s(6)=197
   ```lean
   def littleSchroeder : ℕ → ℕ
     | 0 => 1 | 1 => 1
     | n + 2 => ((6*n+9) * littleSchroeder (n+1) - (n+1) * littleSchroeder n) / (n + 3)
   ```
   Hmm this recurrence might not be exact. Use:
   (n+2)*s(n+1) = (6n+3)*s(n) - (n-1)*s(n-1)... 
   
   Just use table verification.

4. **Binary trees = triangulations:**
   Binary trees with n internal nodes = triangulations of (n+2)-gon = Catalan(n).
   This is a bijection theorem. Just verify numerically.

5. **Stack-sortable permutations:**
   1-stack-sortable permutations of [n] = Catalan(n).
   2-stack-sortable perms of [n]: W_n with W(1)=1, W(2)=2, W(3)=5, W(4)=14, W(5)=42 (= Catalan! but W(6)=132 ≠ Catalan(6)=132... actually they ARE equal up to 5 then diverge at 6: W(6)=132, Cat(6)=132... W(7)=429? Cat(7)=429... Actually 2-stack-sortable = Catalan too? No!
   
   Let me just do: 1-stack-sortable = avoids 231 = Catalan.
   Verify: number of 231-avoiding permutations = C_n for n=1..6.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.PlanarMaps`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace PlanarMaps`** and close with `end PlanarMaps`
- Focus on what's easy to verify. Delete anything with uncertain formulas.

## Output

Write file, verify build, report.
