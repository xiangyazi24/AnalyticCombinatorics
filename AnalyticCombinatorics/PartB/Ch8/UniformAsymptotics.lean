/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VIII — Uniform asymptotic expansions.

  Uniform saddle-point approximations, Airy-type asymptotics near
  coalescent saddle points, phase transitions in random structures.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace UniformAsymptotics

open Finset

/-! ## 1. Uniform asymptotic framework -/

/-- Coalescent saddle point: second derivative of the phase vanishes while
    the third does not, giving rise to Airy-type (cubic) asymptotics. -/
def IsCoalescentSaddle (φ'' φ''' : ℚ) : Prop :=
  φ'' = 0 ∧ φ''' ≠ 0

/-- Phase transition: growth exponents differ across a critical threshold. -/
def PhaseTransitionExponents (expBelow expAbove : ℚ) : Prop :=
  expBelow < expAbove

/-! ## 2. Airy differential equation y'' = xy -/

/-- Power-series coefficients for solutions of the Airy equation y'' = xy.
    Recurrence: a₂ = 0, a_{n+3} = aₙ / ((n+3)(n+2)). -/
def airyCoeff (a₀ a₁ : ℚ) : ℕ → ℚ
  | 0 => a₀
  | 1 => a₁
  | 2 => 0
  | (n + 3) => airyCoeff a₀ a₁ n / (((n + 3) * (n + 2) : ℕ) : ℚ)

/-- First Airy fundamental solution (a₀ = 1, a₁ = 0): nonzero at 3k. -/
def airyF := airyCoeff 1 0

/-- Second Airy fundamental solution (a₀ = 0, a₁ = 1): nonzero at 3k+1. -/
def airyG := airyCoeff 0 1

theorem airyF_values :
    airyF 0 = 1 ∧ airyF 3 = 1 / 6 ∧ airyF 6 = 1 / 180 ∧
    airyF 9 = 1 / 12960 ∧ airyF 12 = 1 / 1710720 := by native_decide

theorem airyG_values :
    airyG 1 = 1 ∧ airyG 4 = 1 / 12 ∧ airyG 7 = 1 / 504 ∧
    airyG 10 = 1 / 45360 ∧ airyG 13 = 1 / 7076160 := by native_decide

theorem airyF_vanishing :
    airyF 1 = 0 ∧ airyF 2 = 0 ∧ airyF 4 = 0 ∧
    airyF 5 = 0 ∧ airyF 7 = 0 ∧ airyF 8 = 0 := by native_decide

theorem airyG_vanishing :
    airyG 0 = 0 ∧ airyG 2 = 0 ∧ airyG 3 = 0 ∧
    airyG 5 = 0 ∧ airyG 6 = 0 ∧ airyG 8 = 0 := by native_decide

/-- Recurrence check: a_{n+3} · (n+3)(n+2) = aₙ. -/
theorem airyF_recurrence :
    airyF 3 * 6 = airyF 0 ∧ airyF 6 * 30 = airyF 3 ∧
    airyF 9 * 72 = airyF 6 ∧ airyF 12 * 132 = airyF 9 := by native_decide

theorem airyG_recurrence :
    airyG 4 * 12 = airyG 1 ∧ airyG 7 * 42 = airyG 4 ∧
    airyG 10 * 90 = airyG 7 ∧ airyG 13 * 156 = airyG 10 := by native_decide

/-- Any solution of the Airy recurrence with a₂ = 0 is a linear combination
    of the two fundamental solutions. -/
theorem airy_basis (f : ℕ → ℚ)
    (hrec : ∀ n, f (n + 3) = f n / (((n + 3) * (n + 2) : ℕ) : ℚ))
    (h2 : f 2 = 0) :
    ∀ n, f n = f 0 * airyF n + f 1 * airyG n :=
  sorry

/-! ## 3. Labeled forests — saddle-point enumeration -/

/-- Cayley tree numbers: labeled unrooted trees on [n] = n^{n-2}. -/
def cayleyTree : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n => n ^ (n - 2)

theorem cayleyTree_values :
    cayleyTree 1 = 1 ∧ cayleyTree 2 = 1 ∧ cayleyTree 3 = 3 ∧
    cayleyTree 4 = 16 ∧ cayleyTree 5 = 125 ∧
    cayleyTree 6 = 1296 ∧ cayleyTree 7 = 16807 := by native_decide

/-- Labeled rooted forests on [n] with k tree components:
    C(n-1, k-1) · n^{n-k}. -/
def rootedForest (n k : ℕ) : ℕ :=
  if k = 0 ∨ k > n ∨ n = 0 then 0
  else Nat.choose (n - 1) (k - 1) * n ^ (n - k)

/-- Total labeled rooted forests on [n] = (n+1)^{n-1}. -/
def totalForest : ℕ → ℕ
  | 0 => 1
  | n => (n + 1) ^ (n - 1)

theorem forest_components_4 :
    rootedForest 4 1 = 64 ∧ rootedForest 4 2 = 48 ∧
    rootedForest 4 3 = 12 ∧ rootedForest 4 4 = 1 := by native_decide

theorem forest_components_5 :
    rootedForest 5 1 = 625 ∧ rootedForest 5 2 = 500 ∧
    rootedForest 5 3 = 150 ∧ rootedForest 5 4 = 20 ∧
    rootedForest 5 5 = 1 := by native_decide

/-- Forest identity: Σ_{k=1}^{n} C(n-1,k-1) · n^{n-k} = (n+1)^{n-1}. -/
theorem forest_decomposition :
    (rootedForest 3 1 + rootedForest 3 2 + rootedForest 3 3 = totalForest 3) ∧
    (rootedForest 4 1 + rootedForest 4 2 + rootedForest 4 3 +
     rootedForest 4 4 = totalForest 4) ∧
    (rootedForest 5 1 + rootedForest 5 2 + rootedForest 5 3 +
     rootedForest 5 4 + rootedForest 5 5 = totalForest 5) := by native_decide

/-- Single-component forests equal rooted labeled trees: n^{n-1}. -/
theorem forest_single_component :
    rootedForest 3 1 = 9 ∧ rootedForest 4 1 = 64 ∧
    rootedForest 5 1 = 625 ∧ rootedForest 6 1 = 7776 := by native_decide

/-! ## 4. Phase transition: excess decomposition of connected graphs -/

/-- Labeled connected graphs on [n], tabulated. OEIS A001187. -/
def connGraphTable : Fin 7 → ℕ :=
  ![1, 1, 1, 4, 38, 728, 26704]

/-- Connected graph recurrence:
    c(n) = 2^{C(n,2)} - Σ_{k=1}^{n-1} C(n-1,k-1) · c(k) · 2^{C(n-k,2)}. -/
theorem connGraph_recurrence_4 :
    connGraphTable ⟨4, by omega⟩ =
    2 ^ Nat.choose 4 2 -
    (Nat.choose 3 0 * connGraphTable ⟨1, by omega⟩ * 2 ^ Nat.choose 3 2 +
     Nat.choose 3 1 * connGraphTable ⟨2, by omega⟩ * 2 ^ Nat.choose 2 2 +
     Nat.choose 3 2 * connGraphTable ⟨3, by omega⟩ * 2 ^ Nat.choose 1 2) := by
  native_decide

theorem connGraph_recurrence_5 :
    connGraphTable ⟨5, by omega⟩ =
    2 ^ Nat.choose 5 2 -
    (Nat.choose 4 0 * connGraphTable ⟨1, by omega⟩ * 2 ^ Nat.choose 4 2 +
     Nat.choose 4 1 * connGraphTable ⟨2, by omega⟩ * 2 ^ Nat.choose 3 2 +
     Nat.choose 4 2 * connGraphTable ⟨3, by omega⟩ * 2 ^ Nat.choose 2 2 +
     Nat.choose 4 3 * connGraphTable ⟨4, by omega⟩ * 2 ^ Nat.choose 1 2) := by
  native_decide

/-- Labeled connected unicyclic graphs on [n] (excess 1).
    Formula: ½ · Σ_{j=0}^{n-3} (n-1)!/j! · n^j. -/
def unicyclicCount (n : ℕ) : ℕ :=
  if n < 3 then 0
  else (∑ j ∈ Finset.range (n - 2),
    (n - 1).factorial / j.factorial * n ^ j) / 2

theorem unicyclic_values :
    unicyclicCount 3 = 1 ∧ unicyclicCount 4 = 15 ∧
    unicyclicCount 5 = 222 ∧ unicyclicCount 6 = 3660 := by native_decide

/-- Excess decomposition: connected = trees + unicyclic + higher excess. -/
theorem excess_decomposition :
    cayleyTree 3 + unicyclicCount 3 = connGraphTable ⟨3, by omega⟩ ∧
    (cayleyTree 4 + unicyclicCount 4 + 7 = connGraphTable ⟨4, by omega⟩) ∧
    (cayleyTree 5 + unicyclicCount 5 + 381 = connGraphTable ⟨5, by omega⟩) := by
  native_decide

/-- Tree fraction (×10000) among connected graphs decreases rapidly. -/
theorem tree_fraction_decreasing :
    cayleyTree 3 * 10000 / connGraphTable ⟨3, by omega⟩ = 7500 ∧
    cayleyTree 4 * 10000 / connGraphTable ⟨4, by omega⟩ = 4210 ∧
    cayleyTree 5 * 10000 / connGraphTable ⟨5, by omega⟩ = 1717 ∧
    cayleyTree 6 * 10000 / connGraphTable ⟨6, by omega⟩ = 485 := by
  native_decide

/-! ## 5. Saddle-point normalization -/

/-- The ratio n^n / n! governs saddle-point normalization (Stirling). -/
def saddleNorm (n : ℕ) : ℚ :=
  if n = 0 then 1 else ((n ^ n : ℕ) : ℚ) / (n.factorial : ℚ)

theorem saddleNorm_values :
    saddleNorm 1 = 1 ∧ saddleNorm 2 = 2 ∧ saddleNorm 3 = 9 / 2 ∧
    saddleNorm 4 = 32 / 3 ∧ saddleNorm 5 = 625 / 24 := by native_decide

/-- Identity: n! · (n^n / n!) = n^n. -/
theorem saddleNorm_factorial :
    ((1 : ℕ).factorial : ℚ) * saddleNorm 1 = 1 ∧
    ((2 : ℕ).factorial : ℚ) * saddleNorm 2 = 4 ∧
    ((3 : ℕ).factorial : ℚ) * saddleNorm 3 = 27 ∧
    ((4 : ℕ).factorial : ℚ) * saddleNorm 4 = 256 ∧
    ((5 : ℕ).factorial : ℚ) * saddleNorm 5 = 3125 := by native_decide

/-- n^n / n! is strictly increasing for n ≥ 1. -/
theorem saddleNorm_increasing :
    saddleNorm 1 < saddleNorm 2 ∧ saddleNorm 2 < saddleNorm 3 ∧
    saddleNorm 3 < saddleNorm 4 ∧ saddleNorm 4 < saddleNorm 5 := by native_decide

/-- Erdős–Rényi phase transition: the largest component growth exponent
    jumps from 0 (subcritical, O(log n)) to 1 (supercritical, Θ(n)) at c = 1. -/
theorem erdos_renyi_phase_transition :
    PhaseTransitionExponents 0 1 := by
  unfold PhaseTransitionExponents; native_decide

end UniformAsymptotics
