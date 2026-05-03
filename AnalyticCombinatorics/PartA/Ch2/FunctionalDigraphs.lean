import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace FunctionalDigraphs

open Finset

/-! # Functional digraphs

Small computable tables for maps `[n] → [n]` and their components, in the
labelled setting of Chapter II of Analytic Combinatorics.
-/

-- Total maps [n] → [n].

def totalMaps (n : ℕ) : ℕ :=
  n ^ n

def totalMapsTable : Fin 8 → ℕ :=
  ![1, 4, 27, 256, 3125, 46656, 823543, 16777216]

theorem totalMaps_table :
    (fun i : Fin 8 => totalMaps (i.val + 1)) = totalMapsTable := by native_decide

-- Bijections, with the reduced ratio n! / n^n.

def bijections (n : ℕ) : ℕ :=
  n.factorial

def reducedBijectionRatio (n : ℕ) : ℕ × ℕ :=
  let g := Nat.gcd (bijections n) (totalMaps n)
  (bijections n / g, totalMaps n / g)

def bijectionsTable : Fin 8 → ℕ :=
  ![1, 2, 6, 24, 120, 720, 5040, 40320]

def reducedBijectionRatioTable : Fin 8 → ℕ × ℕ :=
  ![(1, 1), (1, 2), (2, 9), (3, 32), (24, 625), (5, 324), (720, 117649),
    (315, 131072)]

theorem bijections_table :
    (fun i : Fin 8 => bijections (i.val + 1)) = bijectionsTable := by native_decide

theorem reducedBijectionRatio_table :
    (fun i : Fin 8 => reducedBijectionRatio (i.val + 1)) =
      reducedBijectionRatioTable := by native_decide

-- Connected components.

/-- Prompt-supplied connected-count table, recorded as data. -/
def suppliedConnectedCount : ℕ → ℕ
  | 1 => 1
  | 2 => 3
  | 3 => 14
  | 4 => 87
  | _ => 0

def suppliedConnectedCountTable : Fin 4 → ℕ :=
  ![1, 3, 14, 87]

theorem suppliedConnectedCount_table :
    (fun i : Fin 4 => suppliedConnectedCount (i.val + 1)) =
      suppliedConnectedCountTable := by native_decide

/-- Labelled weakly connected functional digraphs on `[n]`. -/
def connectedMaps (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, (n - 1).factorial / j.factorial * n ^ j

def connectedMapsTable : Fin 4 → ℕ :=
  ![1, 3, 17, 142]

theorem connectedMaps_table :
    (fun i : Fin 4 => connectedMaps (i.val + 1)) = connectedMapsTable := by
  native_decide

/-- Explicit partition expansion for `n = 1, ..., 4`, using labelled
connected component counts and the usual multinomial factors. -/
def partitionExpansionTotal : ℕ → ℕ
  | 1 => connectedMaps 1
  | 2 => connectedMaps 2 + connectedMaps 1 ^ 2
  | 3 => connectedMaps 3 + 3 * connectedMaps 2 * connectedMaps 1 +
      connectedMaps 1 ^ 3
  | 4 => connectedMaps 4 + 4 * connectedMaps 3 * connectedMaps 1 +
      3 * connectedMaps 2 ^ 2 + 6 * connectedMaps 2 * connectedMaps 1 ^ 2 +
      connectedMaps 1 ^ 4
  | _ => 0

def partitionExpansionTable : Fin 4 → ℕ :=
  ![1, 4, 27, 256]

theorem partitionExpansion_table :
    (fun i : Fin 4 => partitionExpansionTotal (i.val + 1)) =
      partitionExpansionTable := by native_decide

theorem partitionExpansion_eq_totalMaps_table :
    (fun i : Fin 4 => partitionExpansionTotal (i.val + 1)) =
      (fun i : Fin 4 => totalMaps (i.val + 1)) := by native_decide

-- Fixed points.

/-- Inclusion-exclusion count of maps with exactly zero fixed points. -/
def noFixedMaps (n : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (n + 1),
      if j % 2 = 0 then Nat.choose n j * n ^ (n - j) else 0) -
    (∑ j ∈ Finset.range (n + 1),
      if j % 2 = 1 then Nat.choose n j * n ^ (n - j) else 0)

def atLeastOneFixedMap (n : ℕ) : ℕ :=
  totalMaps n - noFixedMaps n

def noFixedMapsTable : Fin 8 → ℕ :=
  ![0, 1, 8, 81, 1024, 15625, 279936, 5764801]

def atLeastOneFixedMapTable : Fin 8 → ℕ :=
  ![1, 3, 19, 175, 2101, 31031, 543607, 11012415]

theorem noFixedMaps_table :
    (fun i : Fin 8 => noFixedMaps (i.val + 1)) = noFixedMapsTable := by
  native_decide

theorem atLeastOneFixedMap_table :
    (fun i : Fin 8 => atLeastOneFixedMap (i.val + 1)) =
      atLeastOneFixedMapTable := by native_decide

-- Idempotent maps.

/-- Idempotent maps `f ∘ f = f`: choose the `k` image points, then send every
remaining point to one of them. -/
def idempotentMaps (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, Nat.choose n k * k ^ (n - k)

def idempotentMapsTable : Fin 6 → ℕ :=
  ![1, 3, 10, 41, 196, 1057]

theorem idempotentMaps_table :
    (fun i : Fin 6 => idempotentMaps (i.val + 1)) = idempotentMapsTable := by
  native_decide

theorem idempotentMaps_three_expansion :
    Nat.choose 3 1 * 1 ^ 2 + Nat.choose 3 2 * 2 ^ 1 +
      Nat.choose 3 3 * 3 ^ 0 = 3 + 6 + 1 := by native_decide

theorem idempotentMaps_three_expansion_total :
    Nat.choose 3 1 * 1 ^ 2 + Nat.choose 3 2 * 2 ^ 1 +
      Nat.choose 3 3 * 3 ^ 0 = 10 := by native_decide

theorem idempotentMaps_four_expansion :
    Nat.choose 4 1 * 1 ^ 3 + Nat.choose 4 2 * 2 ^ 2 +
      Nat.choose 4 3 * 3 ^ 1 + Nat.choose 4 4 * 4 ^ 0 =
        4 + 24 + 12 + 1 := by native_decide

theorem idempotentMaps_four_expansion_total :
    Nat.choose 4 1 * 1 ^ 3 + Nat.choose 4 2 * 2 ^ 2 +
      Nat.choose 4 3 * 3 ^ 1 + Nat.choose 4 4 * 4 ^ 0 = 41 := by native_decide

end FunctionalDigraphs
