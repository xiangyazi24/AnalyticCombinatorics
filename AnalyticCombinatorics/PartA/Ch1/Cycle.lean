import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cycle construction schemas.

Cycles of labelled atoms are represented by their direct count sequence:
there are `(n - 1)!` cycles at positive size `n`.
-/

namespace AnalyticCombinatorics.PartA.Ch1.Cycle

def cycleCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => n.factorial

def cycleIndexWeight (period orbitCount : ℕ) : ℕ :=
  period * orbitCount

def cycleEGFDenominator (n : ℕ) : ℕ :=
  n

def labelledCycleSlots (n : ℕ) : ℕ :=
  n * cycleCount n

def pointedCycleCount (n : ℕ) : ℕ :=
  n * cycleCount n

structure CycleWindow where
  atomCount : ℕ
  rotationChecks : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def nonemptyCycle (w : CycleWindow) : Prop :=
  0 < w.atomCount

def rotationsControlled (w : CycleWindow) : Prop :=
  w.rotationChecks ≤ w.atomCount + w.slack

def cycleWindowReady (w : CycleWindow) : Prop :=
  nonemptyCycle w ∧ rotationsControlled w

def cycleWindowBudget (w : CycleWindow) : ℕ :=
  w.atomCount + w.rotationChecks + w.slack

theorem cycleWindowReady.certificate {w : CycleWindow}
    (h : cycleWindowReady w) :
    nonemptyCycle w ∧ rotationsControlled w ∧
      w.rotationChecks ≤ cycleWindowBudget w := by
  rcases h with ⟨hcycle, hcontrolled⟩
  refine ⟨hcycle, hcontrolled, ?_⟩
  unfold cycleWindowBudget
  omega

theorem atomCount_le_budget (w : CycleWindow) :
    w.atomCount ≤ cycleWindowBudget w := by
  unfold cycleWindowBudget
  omega

theorem cycleCount_zero : cycleCount 0 = 0 := by
  native_decide

theorem cycleCount_succ (n : ℕ) :
    cycleCount (n + 1) = n.factorial := by
  rfl

theorem pointedCycle_eq_slots (n : ℕ) :
    pointedCycleCount n = labelledCycleSlots n := by
  rfl

def sampleCycleWindow : CycleWindow :=
  { atomCount := 5, rotationChecks := 6, slack := 2 }

example : cycleWindowReady sampleCycleWindow := by
  norm_num [cycleWindowReady, nonemptyCycle]
  norm_num [rotationsControlled, sampleCycleWindow]

example : cycleCount 1 = 1 := by native_decide
example : cycleCount 4 = 6 := by native_decide
example : cycleCount 7 = 720 := by native_decide
example : pointedCycleCount 4 = 24 := by native_decide
example : cycleWindowBudget sampleCycleWindow = 13 := by native_decide
example : cycleIndexWeight 3 10 = 30 := by native_decide
example : cycleEGFDenominator 7 = 7 := by native_decide
example : labelledCycleSlots 5 = 120 := by native_decide


structure CycleBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CycleBudgetCertificate.controlled
    (c : CycleBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CycleBudgetCertificate.budgetControlled
    (c : CycleBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CycleBudgetCertificate.Ready
    (c : CycleBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CycleBudgetCertificate.size
    (c : CycleBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cycle_budgetCertificate_le_size
    (c : CycleBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCycleBudgetCertificate :
    CycleBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCycleBudgetCertificate.Ready := by
  constructor
  · norm_num [CycleBudgetCertificate.controlled,
      sampleCycleBudgetCertificate]
  · norm_num [CycleBudgetCertificate.budgetControlled,
      sampleCycleBudgetCertificate]

example :
    sampleCycleBudgetCertificate.certificateBudgetWindow ≤
      sampleCycleBudgetCertificate.size := by
  apply cycle_budgetCertificate_le_size
  constructor
  · norm_num [CycleBudgetCertificate.controlled,
      sampleCycleBudgetCertificate]
  · norm_num [CycleBudgetCertificate.budgetControlled,
      sampleCycleBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCycleBudgetCertificate.Ready := by
  constructor
  · norm_num [CycleBudgetCertificate.controlled,
      sampleCycleBudgetCertificate]
  · norm_num [CycleBudgetCertificate.budgetControlled,
      sampleCycleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCycleBudgetCertificate.certificateBudgetWindow ≤
      sampleCycleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CycleBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCycleBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCycleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.Cycle
