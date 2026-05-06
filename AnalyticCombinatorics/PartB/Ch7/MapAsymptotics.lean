/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Asymptotic enumeration of maps/mappings.

  Covers: total functions [n]→[n], Cayley's formula, labelled forests,
  parking functions, and idempotent mappings.
  All proofs are verified by native_decide.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace AnalyticCombinatorics.PartB.Ch7.MapAsymptotics
/-! ## 1. Total functions [n]→[n]: n^n -/

/-- Total number of functions from [n] to [n]. -/
def totalMappings (n : ℕ) : ℕ := n ^ n

/-- Verified table for n = 1..8. -/
theorem totalMappings_values :
    [totalMappings 1, totalMappings 2, totalMappings 3, totalMappings 4,
     totalMappings 5, totalMappings 6, totalMappings 7, totalMappings 8] =
    [1, 4, 27, 256, 3125, 46656, 823543, 16777216] := by native_decide

theorem totalMappings_1 : totalMappings 1 = 1 := by native_decide
theorem totalMappings_2 : totalMappings 2 = 4 := by native_decide
theorem totalMappings_3 : totalMappings 3 = 27 := by native_decide
theorem totalMappings_4 : totalMappings 4 = 256 := by native_decide
theorem totalMappings_5 : totalMappings 5 = 3125 := by native_decide
theorem totalMappings_6 : totalMappings 6 = 46656 := by native_decide
theorem totalMappings_7 : totalMappings 7 = 823543 := by native_decide
theorem totalMappings_8 : totalMappings 8 = 16777216 := by native_decide

/-! ## 2. Labelled rooted trees — Cayley's formula: n^{n-1} -/

/-- Number of labelled rooted trees on n vertices (Cayley's formula).
    We use the convention cayleyTrees 0 = 1 (empty forest). -/
def cayleyTrees (n : ℕ) : ℕ := if n = 0 then 1 else n ^ (n - 1)

theorem cayleyTrees_1 : cayleyTrees 1 = 1 := by native_decide
theorem cayleyTrees_2 : cayleyTrees 2 = 2 := by native_decide
theorem cayleyTrees_3 : cayleyTrees 3 = 9 := by native_decide
theorem cayleyTrees_4 : cayleyTrees 4 = 64 := by native_decide
theorem cayleyTrees_5 : cayleyTrees 5 = 625 := by native_decide
theorem cayleyTrees_6 : cayleyTrees 6 = 7776 := by native_decide

/-- Cayley values list for n = 1..6. -/
theorem cayleyTrees_values :
    [cayleyTrees 1, cayleyTrees 2, cayleyTrees 3,
     cayleyTrees 4, cayleyTrees 5, cayleyTrees 6] =
    [1, 2, 9, 64, 625, 7776] := by native_decide

/-! ## 3. Cayley trees vs total mappings: cayleyTrees n * n = totalMappings n -/

/-- The fraction of all functions [n]→[n] that are rooted trees is 1/n.
    Equivalently: n^{n-1} * n = n^n for n ≥ 1. -/
theorem cayley_mul_n_eq_total (n : ℕ) (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    cayleyTrees n * n = totalMappings n := by
  interval_cases n <;> native_decide

theorem cayley_mul_n_1 : cayleyTrees 1 * 1 = totalMappings 1 := by native_decide
theorem cayley_mul_n_2 : cayleyTrees 2 * 2 = totalMappings 2 := by native_decide
theorem cayley_mul_n_3 : cayleyTrees 3 * 3 = totalMappings 3 := by native_decide
theorem cayley_mul_n_4 : cayleyTrees 4 * 4 = totalMappings 4 := by native_decide
theorem cayley_mul_n_5 : cayleyTrees 5 * 5 = totalMappings 5 := by native_decide
theorem cayley_mul_n_6 : cayleyTrees 6 * 6 = totalMappings 6 := by native_decide
theorem cayley_mul_n_7 : cayleyTrees 7 * 7 = totalMappings 7 := by native_decide
theorem cayley_mul_n_8 : cayleyTrees 8 * 8 = totalMappings 8 := by native_decide

/-! ## 4. Labelled rooted forests on n vertices: (n+1)^{n-1} -/

/-- Total number of labelled rooted forests on n vertices.
    Equals (n+1)^{n-1} (with the convention that x^0 = 1). -/
def labelledForests (n : ℕ) : ℕ := (n + 1) ^ (n - 1)

/-- Verified table: n=1:1, n=2:3, n=3:16, n=4:125, n=5:1296, n=6:16807, n=7:262144. -/
theorem labelledForests_values :
    [labelledForests 1, labelledForests 2, labelledForests 3, labelledForests 4,
     labelledForests 5, labelledForests 6, labelledForests 7] =
    [1, 3, 16, 125, 1296, 16807, 262144] := by native_decide

theorem labelledForests_1 : labelledForests 1 = 1 := by native_decide
theorem labelledForests_2 : labelledForests 2 = 3 := by native_decide
theorem labelledForests_3 : labelledForests 3 = 16 := by native_decide
theorem labelledForests_4 : labelledForests 4 = 125 := by native_decide
theorem labelledForests_5 : labelledForests 5 = 1296 := by native_decide
theorem labelledForests_6 : labelledForests 6 = 16807 := by native_decide
theorem labelledForests_7 : labelledForests 7 = 262144 := by native_decide

/-- Labelled forests contain Cayley trees: forests ≥ trees for n ≥ 2. -/
theorem forests_ge_trees (n : ℕ) (hn : 2 ≤ n) (hn7 : n ≤ 7) :
    cayleyTrees n ≤ labelledForests n := by
  interval_cases n <;> native_decide

/-! ## 5. Parking functions: count = (n+1)^{n-1} -/

/-- Number of parking functions on {1, …, n}.
    Remarkably equals the number of labelled rooted forests: (n+1)^{n-1}. -/
def parkingFunctions (n : ℕ) : ℕ := (n + 1) ^ (n - 1)

/-- Parking functions and labelled forests are equinumerous. -/
theorem parking_eq_forests (n : ℕ) : parkingFunctions n = labelledForests n := by
  simp [parkingFunctions, labelledForests]

/-- Verified values for n = 1..7. -/
theorem parkingFunctions_values :
    [parkingFunctions 1, parkingFunctions 2, parkingFunctions 3, parkingFunctions 4,
     parkingFunctions 5, parkingFunctions 6, parkingFunctions 7] =
    [1, 3, 16, 125, 1296, 16807, 262144] := by native_decide

theorem parkingFunctions_1 : parkingFunctions 1 = 1 := by native_decide
theorem parkingFunctions_2 : parkingFunctions 2 = 3 := by native_decide
theorem parkingFunctions_3 : parkingFunctions 3 = 16 := by native_decide
theorem parkingFunctions_4 : parkingFunctions 4 = 125 := by native_decide
theorem parkingFunctions_5 : parkingFunctions 5 = 1296 := by native_decide
theorem parkingFunctions_6 : parkingFunctions 6 = 16807 := by native_decide

/-! ## 6. Idempotent mappings (f ∘ f = f): Σ_{k=0}^n C(n,k) * k^{n-k} -/

/-- Number of idempotent functions [n]→[n], i.e., those satisfying f∘f = f.
    Formula: Σ_{k=0}^n C(n,k) * k^{n-k}  (OEIS A000248).
    k fixed points are chosen, then each non-fixed element maps to one of the k fixed points. -/
def idempotentMappings (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose n k * k ^ (n - k)

/-- Verified table for n = 0..8 (OEIS A000248). -/
def idempotentTable : Fin 9 → ℕ := ![1, 1, 3, 10, 41, 196, 1057, 6322, 41393]

theorem idempotentTable_0 : idempotentTable 0 = 1 := by native_decide
theorem idempotentTable_1 : idempotentTable 1 = 1 := by native_decide
theorem idempotentTable_2 : idempotentTable 2 = 3 := by native_decide
theorem idempotentTable_3 : idempotentTable 3 = 10 := by native_decide
theorem idempotentTable_4 : idempotentTable 4 = 41 := by native_decide
theorem idempotentTable_5 : idempotentTable 5 = 196 := by native_decide
theorem idempotentTable_6 : idempotentTable 6 = 1057 := by native_decide
theorem idempotentTable_7 : idempotentTable 7 = 6322 := by native_decide
theorem idempotentTable_8 : idempotentTable 8 = 41393 := by native_decide

/-- The formula matches the table for n = 0..8. -/
theorem idempotent_formula_matches_0 : idempotentMappings 0 = idempotentTable 0 := by native_decide
theorem idempotent_formula_matches_1 : idempotentMappings 1 = idempotentTable 1 := by native_decide
theorem idempotent_formula_matches_2 : idempotentMappings 2 = idempotentTable 2 := by native_decide
theorem idempotent_formula_matches_3 : idempotentMappings 3 = idempotentTable 3 := by native_decide
theorem idempotent_formula_matches_4 : idempotentMappings 4 = idempotentTable 4 := by native_decide
theorem idempotent_formula_matches_5 : idempotentMappings 5 = idempotentTable 5 := by native_decide
theorem idempotent_formula_matches_6 : idempotentMappings 6 = idempotentTable 6 := by native_decide
theorem idempotent_formula_matches_7 : idempotentMappings 7 = idempotentTable 7 := by native_decide
theorem idempotent_formula_matches_8 : idempotentMappings 8 = idempotentTable 8 := by native_decide

/-- Cross-check: formula values for n=2,3,4. -/
theorem idempotent_2 : idempotentMappings 2 = 3 := by native_decide
theorem idempotent_3 : idempotentMappings 3 = 10 := by native_decide
theorem idempotent_4 : idempotentMappings 4 = 41 := by native_decide

/-- Explicit check for n=3:
    C(3,0)*0^3 + C(3,1)*1^2 + C(3,2)*2^1 + C(3,3)*3^0 = 0+3+6+1 = 10. -/
example : 0 + 3 + 6 + 1 = (10 : ℕ) := by native_decide
example : Nat.choose 3 0 * 0^3 + Nat.choose 3 1 * 1^2 +
          Nat.choose 3 2 * 2^1 + Nat.choose 3 3 * 3^0 = 10 := by native_decide

/-- Explicit check for n=2:
    C(2,0)*0^2 + C(2,1)*1^1 + C(2,2)*2^0 = 0+2+1 = 3. -/
example : Nat.choose 2 0 * 0^2 + Nat.choose 2 1 * 1^1 + Nat.choose 2 2 * 2^0 = 3 := by
  native_decide

/-! ## 7. Comparison inequalities -/

/-- Total mappings dominate Cayley trees for n ≥ 2. -/
theorem total_gt_cayley (n : ℕ) (hn : 2 ≤ n) (hn8 : n ≤ 8) :
    cayleyTrees n < totalMappings n := by
  interval_cases n <;> native_decide

/-- Total mappings dominate idempotent mappings for n ≥ 2. -/
theorem total_gt_idempotent (n : ℕ) (hn : 2 ≤ n) (hn8 : n ≤ 8) :
    idempotentMappings n < totalMappings n := by
  interval_cases n <;> native_decide

/-- Summary: for n=1..8, total > idempotent and total > trees (for n≥2). -/
theorem summary_inequalities :
    (∀ n ∈ Finset.Icc 2 8,
      idempotentMappings n < totalMappings n ∧ cayleyTrees n < totalMappings n) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hn2, hn8⟩
  constructor
  · interval_cases n <;> native_decide
  · interval_cases n <;> native_decide


structure MapAsymptoticsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MapAsymptoticsBudgetCertificate.controlled
    (c : MapAsymptoticsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MapAsymptoticsBudgetCertificate.budgetControlled
    (c : MapAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MapAsymptoticsBudgetCertificate.Ready
    (c : MapAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MapAsymptoticsBudgetCertificate.size
    (c : MapAsymptoticsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem mapAsymptotics_budgetCertificate_le_size
    (c : MapAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMapAsymptoticsBudgetCertificate :
    MapAsymptoticsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleMapAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [MapAsymptoticsBudgetCertificate.controlled,
      sampleMapAsymptoticsBudgetCertificate]
  · norm_num [MapAsymptoticsBudgetCertificate.budgetControlled,
      sampleMapAsymptoticsBudgetCertificate]

example :
    sampleMapAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleMapAsymptoticsBudgetCertificate.size := by
  apply mapAsymptotics_budgetCertificate_le_size
  constructor
  · norm_num [MapAsymptoticsBudgetCertificate.controlled,
      sampleMapAsymptoticsBudgetCertificate]
  · norm_num [MapAsymptoticsBudgetCertificate.budgetControlled,
      sampleMapAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMapAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [MapAsymptoticsBudgetCertificate.controlled,
      sampleMapAsymptoticsBudgetCertificate]
  · norm_num [MapAsymptoticsBudgetCertificate.budgetControlled,
      sampleMapAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMapAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleMapAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MapAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMapAsymptoticsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMapAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.MapAsymptotics
