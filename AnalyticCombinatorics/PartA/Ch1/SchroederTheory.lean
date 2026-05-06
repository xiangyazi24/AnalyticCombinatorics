import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Schroeder count table.

The large Schroeder numbers satisfy `S = 1 + z*S + z*S^2`; the finite
certificate below records the recurrence data used by the first values.
-/

namespace AnalyticCombinatorics.PartA.Ch1.SchroederTheory

structure SchroederWindow where
  leafCount : ℕ
  largeBranchCount : ℕ
  branchingSlack : ℕ
deriving DecidableEq, Repr

def nonemptySchroederFamily (w : SchroederWindow) : Prop :=
  0 < w.leafCount

def largeBranchesControlled (w : SchroederWindow) : Prop :=
  w.largeBranchCount ≤ w.leafCount + w.branchingSlack

def schroederWindowReady (w : SchroederWindow) : Prop :=
  nonemptySchroederFamily w ∧ largeBranchesControlled w

def schroederWindowBudget (w : SchroederWindow) : ℕ :=
  w.leafCount + w.largeBranchCount + w.branchingSlack

theorem schroederWindowReady.certificate {w : SchroederWindow}
    (h : schroederWindowReady w) :
    nonemptySchroederFamily w ∧ largeBranchesControlled w ∧
      w.largeBranchCount ≤ schroederWindowBudget w := by
  rcases h with ⟨hleaves, hcontrolled⟩
  refine ⟨hleaves, hcontrolled, ?_⟩
  unfold schroederWindowBudget
  omega

theorem leafCount_le_budget (w : SchroederWindow) :
    w.leafCount ≤ schroederWindowBudget w := by
  unfold schroederWindowBudget
  omega

def schroederConvolution (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), a i * a (n - i)

def schroederStep (previous quadratic : ℕ) : ℕ :=
  previous + quadratic

def schroederCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 22
  | 4 => 90
  | 5 => 394
  | _ => 0

def schroederRecurrenceCheck (n : ℕ) : Prop :=
  schroederCount (n + 1) =
    schroederStep (schroederCount n) (schroederConvolution schroederCount n)

def sampleSchroederWindow : SchroederWindow :=
  { leafCount := 6, largeBranchCount := 7, branchingSlack := 2 }

example : schroederWindowReady sampleSchroederWindow := by
  norm_num [schroederWindowReady, nonemptySchroederFamily]
  norm_num [largeBranchesControlled, sampleSchroederWindow]

example :
    schroederCount 1 =
      schroederStep (schroederCount 0) (schroederConvolution schroederCount 0) := by
  native_decide

example :
    schroederCount 2 =
      schroederStep (schroederCount 1) (schroederConvolution schroederCount 1) := by
  native_decide

example :
    schroederCount 3 =
      schroederStep (schroederCount 2) (schroederConvolution schroederCount 2) := by
  native_decide

example :
    schroederCount 4 =
      schroederStep (schroederCount 3) (schroederConvolution schroederCount 3) := by
  native_decide
example : schroederCount 5 = 394 := by native_decide
example : schroederConvolution schroederCount 3 = 68 := by native_decide
example : schroederWindowBudget sampleSchroederWindow = 15 := by native_decide


structure SchroederTheoryBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SchroederTheoryBudgetCertificate.controlled
    (c : SchroederTheoryBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SchroederTheoryBudgetCertificate.budgetControlled
    (c : SchroederTheoryBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SchroederTheoryBudgetCertificate.Ready
    (c : SchroederTheoryBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SchroederTheoryBudgetCertificate.size
    (c : SchroederTheoryBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem schroederTheory_budgetCertificate_le_size
    (c : SchroederTheoryBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSchroederTheoryBudgetCertificate :
    SchroederTheoryBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSchroederTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [SchroederTheoryBudgetCertificate.controlled,
      sampleSchroederTheoryBudgetCertificate]
  · norm_num [SchroederTheoryBudgetCertificate.budgetControlled,
      sampleSchroederTheoryBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSchroederTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleSchroederTheoryBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSchroederTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [SchroederTheoryBudgetCertificate.controlled,
      sampleSchroederTheoryBudgetCertificate]
  · norm_num [SchroederTheoryBudgetCertificate.budgetControlled,
      sampleSchroederTheoryBudgetCertificate]

example :
    sampleSchroederTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleSchroederTheoryBudgetCertificate.size := by
  apply schroederTheory_budgetCertificate_le_size
  constructor
  · norm_num [SchroederTheoryBudgetCertificate.controlled,
      sampleSchroederTheoryBudgetCertificate]
  · norm_num [SchroederTheoryBudgetCertificate.budgetControlled,
      sampleSchroederTheoryBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SchroederTheoryBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSchroederTheoryBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSchroederTheoryBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.SchroederTheory
