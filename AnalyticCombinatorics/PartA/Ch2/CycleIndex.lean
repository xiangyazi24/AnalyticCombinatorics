import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cycle index schemas.
-/

namespace AnalyticCombinatorics.PartA.Ch2.CycleIndex

structure CycleIndexProfile where
  fixedPoints : ℕ
  transpositions : ℕ
  longerCycles : ℕ
deriving DecidableEq, Repr

def CycleIndexProfile.totalCycles (p : CycleIndexProfile) : ℕ :=
  p.fixedPoints + p.transpositions + p.longerCycles

def CycleIndexProfile.movedAtoms (p : CycleIndexProfile) : ℕ :=
  p.fixedPoints + 2 * p.transpositions + 3 * p.longerCycles

def cycleIndexTermBudget (cycleTypes variableCount slack : ℕ) : ℕ :=
  cycleTypes + variableCount + slack

def cycleIndexWindowReady (cycleTypes variableCount slack : ℕ) : Prop :=
  0 < cycleTypes ∧ variableCount ≤ cycleTypes + slack

def cycleIndexProfileReady (p : CycleIndexProfile) : Prop :=
  0 < p.totalCycles ∧ p.totalCycles ≤ p.movedAtoms

def cycleIndexWeight (p : CycleIndexProfile) : ℕ :=
  p.movedAtoms + p.totalCycles

theorem variableCount_le_budget (cycleTypes variableCount slack : ℕ) :
    variableCount ≤ cycleIndexTermBudget cycleTypes variableCount slack := by
  unfold cycleIndexTermBudget
  omega

theorem cycleIndexProfileReady.certificate {p : CycleIndexProfile}
    (h : cycleIndexProfileReady p) :
    0 < p.totalCycles ∧ p.totalCycles ≤ p.movedAtoms ∧
      p.totalCycles ≤ cycleIndexWeight p := by
  rcases h with ⟨hcycles, hmoved⟩
  refine ⟨hcycles, hmoved, ?_⟩
  unfold cycleIndexWeight
  omega

def sampleCycleIndexProfile : CycleIndexProfile :=
  { fixedPoints := 2, transpositions := 1, longerCycles := 1 }

example : cycleIndexWindowReady 5 7 2 := by
  norm_num [cycleIndexWindowReady]

example : cycleIndexProfileReady sampleCycleIndexProfile := by
  norm_num [cycleIndexProfileReady, CycleIndexProfile.totalCycles,
    CycleIndexProfile.movedAtoms, sampleCycleIndexProfile]

example : cycleIndexTermBudget 5 7 2 = 14 := by native_decide
example : sampleCycleIndexProfile.totalCycles = 4 := by native_decide
example : sampleCycleIndexProfile.movedAtoms = 7 := by native_decide
example : cycleIndexWeight sampleCycleIndexProfile = 11 := by native_decide


structure CycleIndexBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CycleIndexBudgetCertificate.controlled
    (c : CycleIndexBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CycleIndexBudgetCertificate.budgetControlled
    (c : CycleIndexBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CycleIndexBudgetCertificate.Ready
    (c : CycleIndexBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CycleIndexBudgetCertificate.size
    (c : CycleIndexBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cycleIndex_budgetCertificate_le_size
    (c : CycleIndexBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCycleIndexBudgetCertificate :
    CycleIndexBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCycleIndexBudgetCertificate.Ready := by
  constructor
  · norm_num [CycleIndexBudgetCertificate.controlled,
      sampleCycleIndexBudgetCertificate]
  · norm_num [CycleIndexBudgetCertificate.budgetControlled,
      sampleCycleIndexBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCycleIndexBudgetCertificate.certificateBudgetWindow ≤
      sampleCycleIndexBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCycleIndexBudgetCertificate.Ready := by
  constructor
  · norm_num [CycleIndexBudgetCertificate.controlled,
      sampleCycleIndexBudgetCertificate]
  · norm_num [CycleIndexBudgetCertificate.budgetControlled,
      sampleCycleIndexBudgetCertificate]

example :
    sampleCycleIndexBudgetCertificate.certificateBudgetWindow ≤
      sampleCycleIndexBudgetCertificate.size := by
  apply cycleIndex_budgetCertificate_le_size
  constructor
  · norm_num [CycleIndexBudgetCertificate.controlled,
      sampleCycleIndexBudgetCertificate]
  · norm_num [CycleIndexBudgetCertificate.budgetControlled,
      sampleCycleIndexBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CycleIndexBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCycleIndexBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCycleIndexBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.CycleIndex
