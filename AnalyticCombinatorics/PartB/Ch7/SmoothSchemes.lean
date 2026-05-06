/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Smooth implicit-function schemes and finite numerical tables.

  The file records exact small tables for Bell numbers, involutions,
  idempotent maps, pair partitions, and fixed-point-free involutions.
  All proofs are finite arithmetic checks.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch7.SmoothSchemes
-- ============================================================
-- §1 Bell numbers
-- ============================================================

/-- Exact Bell numbers B(0), ..., B(9). -/
def bellTable : Fin 10 → ℕ :=
  ![1, 1, 2, 5, 15, 52, 203, 877, 4140, 21147]

theorem bellTable_0 : bellTable 0 = 1 := by native_decide
theorem bellTable_1 : bellTable 1 = 1 := by native_decide
theorem bellTable_2 : bellTable 2 = 2 := by native_decide
theorem bellTable_3 : bellTable 3 = 5 := by native_decide
theorem bellTable_4 : bellTable 4 = 15 := by native_decide
theorem bellTable_5 : bellTable 5 = 52 := by native_decide
theorem bellTable_6 : bellTable 6 = 203 := by native_decide
theorem bellTable_7 : bellTable 7 = 877 := by native_decide
theorem bellTable_8 : bellTable 8 = 4140 := by native_decide
theorem bellTable_9 : bellTable 9 = 21147 := by native_decide

theorem bellTable_values :
    [bellTable 0, bellTable 1, bellTable 2, bellTable 3, bellTable 4,
     bellTable 5, bellTable 6, bellTable 7, bellTable 8, bellTable 9] =
    [1, 1, 2, 5, 15, 52, 203, 877, 4140, 21147] := by native_decide

theorem bell_lt_factorial_3_to_9 :
    bellTable 3 < Nat.factorial 3 ∧
    bellTable 4 < Nat.factorial 4 ∧
    bellTable 5 < Nat.factorial 5 ∧
    bellTable 6 < Nat.factorial 6 ∧
    bellTable 7 < Nat.factorial 7 ∧
    bellTable 8 < Nat.factorial 8 ∧
    bellTable 9 < Nat.factorial 9 := by native_decide

theorem bell_gt_pow_two_5_to_9 :
    2 ^ 5 < bellTable 5 ∧
    2 ^ 6 < bellTable 6 ∧
    2 ^ 7 < bellTable 7 ∧
    2 ^ 8 < bellTable 8 ∧
    2 ^ 9 < bellTable 9 := by native_decide

-- ============================================================
-- §2 Involutions
-- ============================================================

/-- Exact involution numbers I(0), ..., I(9). -/
def involutionTable : Fin 10 → ℕ :=
  ![1, 1, 2, 4, 10, 26, 76, 232, 764, 2620]

theorem involutionTable_0 : involutionTable 0 = 1 := by native_decide
theorem involutionTable_1 : involutionTable 1 = 1 := by native_decide
theorem involutionTable_2 : involutionTable 2 = 2 := by native_decide
theorem involutionTable_3 : involutionTable 3 = 4 := by native_decide
theorem involutionTable_4 : involutionTable 4 = 10 := by native_decide
theorem involutionTable_5 : involutionTable 5 = 26 := by native_decide
theorem involutionTable_6 : involutionTable 6 = 76 := by native_decide
theorem involutionTable_7 : involutionTable 7 = 232 := by native_decide
theorem involutionTable_8 : involutionTable 8 = 764 := by native_decide
theorem involutionTable_9 : involutionTable 9 = 2620 := by native_decide

theorem involutionTable_values :
    [involutionTable 0, involutionTable 1, involutionTable 2,
     involutionTable 3, involutionTable 4, involutionTable 5,
     involutionTable 6, involutionTable 7, involutionTable 8,
     involutionTable 9] =
    [1, 1, 2, 4, 10, 26, 76, 232, 764, 2620] := by native_decide

theorem involution_rec_2_to_9 :
    involutionTable 2 = involutionTable 1 + 1 * involutionTable 0 ∧
    involutionTable 3 = involutionTable 2 + 2 * involutionTable 1 ∧
    involutionTable 4 = involutionTable 3 + 3 * involutionTable 2 ∧
    involutionTable 5 = involutionTable 4 + 4 * involutionTable 3 ∧
    involutionTable 6 = involutionTable 5 + 5 * involutionTable 4 ∧
    involutionTable 7 = involutionTable 6 + 6 * involutionTable 5 ∧
    involutionTable 8 = involutionTable 7 + 7 * involutionTable 6 ∧
    involutionTable 9 = involutionTable 8 + 8 * involutionTable 7 := by native_decide

-- ============================================================
-- §3 Idempotent maps
-- ============================================================

/-- Exact numbers of idempotent maps on n labelled points, n = 0, ..., 7. -/
def idempotentMapTable : Fin 8 → ℕ :=
  ![1, 1, 3, 10, 41, 196, 1057, 6322]

theorem idempotentMapTable_0 : idempotentMapTable 0 = 1 := by native_decide
theorem idempotentMapTable_1 : idempotentMapTable 1 = 1 := by native_decide
theorem idempotentMapTable_2 : idempotentMapTable 2 = 3 := by native_decide
theorem idempotentMapTable_3 : idempotentMapTable 3 = 10 := by native_decide
theorem idempotentMapTable_4 : idempotentMapTable 4 = 41 := by native_decide
theorem idempotentMapTable_5 : idempotentMapTable 5 = 196 := by native_decide
theorem idempotentMapTable_6 : idempotentMapTable 6 = 1057 := by native_decide
theorem idempotentMapTable_7 : idempotentMapTable 7 = 6322 := by native_decide

theorem idempotentMapTable_values :
    [idempotentMapTable 0, idempotentMapTable 1, idempotentMapTable 2,
     idempotentMapTable 3, idempotentMapTable 4, idempotentMapTable 5,
     idempotentMapTable 6, idempotentMapTable 7] =
    [1, 1, 3, 10, 41, 196, 1057, 6322] := by native_decide

theorem idempotentMap_le_self_power_1_to_7 :
    idempotentMapTable 1 ≤ 1 ^ 1 ∧
    idempotentMapTable 2 ≤ 2 ^ 2 ∧
    idempotentMapTable 3 ≤ 3 ^ 3 ∧
    idempotentMapTable 4 ≤ 4 ^ 4 ∧
    idempotentMapTable 5 ≤ 5 ^ 5 ∧
    idempotentMapTable 6 ≤ 6 ^ 6 ∧
    idempotentMapTable 7 ≤ 7 ^ 7 := by native_decide

-- ============================================================
-- §4 Pair partitions
-- ============================================================

/-- Exact pair partition counts `(2k)! / (2^k * k!)` for k = 1, ..., 5. -/
def pairPartitionTable : Fin 5 → ℕ :=
  ![1, 3, 15, 105, 945]

theorem pairPartitionTable_1 : pairPartitionTable 0 = 1 := by native_decide
theorem pairPartitionTable_2 : pairPartitionTable 1 = 3 := by native_decide
theorem pairPartitionTable_3 : pairPartitionTable 2 = 15 := by native_decide
theorem pairPartitionTable_4 : pairPartitionTable 3 = 105 := by native_decide
theorem pairPartitionTable_5 : pairPartitionTable 4 = 945 := by native_decide

theorem pairPartitionTable_values :
    [pairPartitionTable 0, pairPartitionTable 1, pairPartitionTable 2,
     pairPartitionTable 3, pairPartitionTable 4] =
    [1, 3, 15, 105, 945] := by native_decide

theorem pairPartition_factorial_formula_1_to_5 :
    Nat.factorial (2 * 1) = pairPartitionTable 0 * 2 ^ 1 * Nat.factorial 1 ∧
    Nat.factorial (2 * 2) = pairPartitionTable 1 * 2 ^ 2 * Nat.factorial 2 ∧
    Nat.factorial (2 * 3) = pairPartitionTable 2 * 2 ^ 3 * Nat.factorial 3 ∧
    Nat.factorial (2 * 4) = pairPartitionTable 3 * 2 ^ 4 * Nat.factorial 4 ∧
    Nat.factorial (2 * 5) = pairPartitionTable 4 * 2 ^ 5 * Nat.factorial 5 := by native_decide

-- ============================================================
-- §5 Fixed-point-free involutions
-- ============================================================

/-- Exact fixed-point-free involution counts `(2n - 1)!!` for n = 0, ..., 5. -/
def fixedPointFreeInvolutionTable : Fin 6 → ℕ :=
  ![1, 1, 3, 15, 105, 945]

theorem fixedPointFreeInvolutionTable_0 :
    fixedPointFreeInvolutionTable 0 = 1 := by native_decide
theorem fixedPointFreeInvolutionTable_1 :
    fixedPointFreeInvolutionTable 1 = 1 := by native_decide
theorem fixedPointFreeInvolutionTable_2 :
    fixedPointFreeInvolutionTable 2 = 3 := by native_decide
theorem fixedPointFreeInvolutionTable_3 :
    fixedPointFreeInvolutionTable 3 = 15 := by native_decide
theorem fixedPointFreeInvolutionTable_4 :
    fixedPointFreeInvolutionTable 4 = 105 := by native_decide
theorem fixedPointFreeInvolutionTable_5 :
    fixedPointFreeInvolutionTable 5 = 945 := by native_decide

theorem fixedPointFreeInvolutionTable_values :
    [fixedPointFreeInvolutionTable 0, fixedPointFreeInvolutionTable 1,
     fixedPointFreeInvolutionTable 2, fixedPointFreeInvolutionTable 3,
     fixedPointFreeInvolutionTable 4, fixedPointFreeInvolutionTable 5] =
    [1, 1, 3, 15, 105, 945] := by native_decide

theorem fixedPointFreeInvolution_rec_1_to_5 :
    fixedPointFreeInvolutionTable 1 = 1 * fixedPointFreeInvolutionTable 0 ∧
    fixedPointFreeInvolutionTable 2 = 3 * fixedPointFreeInvolutionTable 1 ∧
    fixedPointFreeInvolutionTable 3 = 5 * fixedPointFreeInvolutionTable 2 ∧
    fixedPointFreeInvolutionTable 4 = 7 * fixedPointFreeInvolutionTable 3 ∧
    fixedPointFreeInvolutionTable 5 = 9 * fixedPointFreeInvolutionTable 4 := by native_decide


structure SmoothSchemesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SmoothSchemesBudgetCertificate.controlled
    (c : SmoothSchemesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SmoothSchemesBudgetCertificate.budgetControlled
    (c : SmoothSchemesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SmoothSchemesBudgetCertificate.Ready
    (c : SmoothSchemesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SmoothSchemesBudgetCertificate.size
    (c : SmoothSchemesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem smoothSchemes_budgetCertificate_le_size
    (c : SmoothSchemesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSmoothSchemesBudgetCertificate :
    SmoothSchemesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSmoothSchemesBudgetCertificate.Ready := by
  constructor
  · norm_num [SmoothSchemesBudgetCertificate.controlled,
      sampleSmoothSchemesBudgetCertificate]
  · norm_num [SmoothSchemesBudgetCertificate.budgetControlled,
      sampleSmoothSchemesBudgetCertificate]

example :
    sampleSmoothSchemesBudgetCertificate.certificateBudgetWindow ≤
      sampleSmoothSchemesBudgetCertificate.size := by
  apply smoothSchemes_budgetCertificate_le_size
  constructor
  · norm_num [SmoothSchemesBudgetCertificate.controlled,
      sampleSmoothSchemesBudgetCertificate]
  · norm_num [SmoothSchemesBudgetCertificate.budgetControlled,
      sampleSmoothSchemesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSmoothSchemesBudgetCertificate.Ready := by
  constructor
  · norm_num [SmoothSchemesBudgetCertificate.controlled,
      sampleSmoothSchemesBudgetCertificate]
  · norm_num [SmoothSchemesBudgetCertificate.budgetControlled,
      sampleSmoothSchemesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSmoothSchemesBudgetCertificate.certificateBudgetWindow ≤
      sampleSmoothSchemesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SmoothSchemesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSmoothSchemesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSmoothSchemesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.SmoothSchemes
