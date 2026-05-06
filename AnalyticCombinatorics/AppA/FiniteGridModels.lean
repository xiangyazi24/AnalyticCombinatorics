import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite grid models.

The module records elementary rectangular-grid counts used by lattice path
and transfer-matrix examples.
-/

namespace AnalyticCombinatorics.AppA.FiniteGridModels

structure GridBox where
  width : ℕ
  height : ℕ
deriving DecidableEq, Repr

def nonemptyGrid (g : GridBox) : Prop :=
  0 < g.width ∧ 0 < g.height

def cellCount (g : GridBox) : ℕ :=
  g.width * g.height

def boundaryBudget (g : GridBox) : ℕ :=
  2 * g.width + 2 * g.height

theorem cellCount_positive {g : GridBox}
    (h : nonemptyGrid g) :
    0 < cellCount g := by
  unfold nonemptyGrid cellCount at *
  exact Nat.mul_pos h.1 h.2

theorem width_le_boundaryBudget (g : GridBox) :
    g.width ≤ boundaryBudget g := by
  unfold boundaryBudget
  omega

def sampleGrid : GridBox :=
  { width := 4, height := 3 }

example : nonemptyGrid sampleGrid := by
  norm_num [nonemptyGrid, sampleGrid]

example : cellCount sampleGrid = 12 := by
  native_decide

example : boundaryBudget sampleGrid = 14 := by
  native_decide

structure GridWindow where
  width : ℕ
  height : ℕ
  cells : ℕ
  boundary : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GridWindow.dimensionReady (w : GridWindow) : Prop :=
  0 < w.width ∧ 0 < w.height

def GridWindow.cellControlled (w : GridWindow) : Prop :=
  w.cells ≤ w.width * w.height + w.slack

def GridWindow.boundaryControlled (w : GridWindow) : Prop :=
  w.boundary ≤ 2 * w.width + 2 * w.height + w.slack

def GridWindow.ready (w : GridWindow) : Prop :=
  w.dimensionReady ∧ w.cellControlled ∧ w.boundaryControlled

def GridWindow.certificate (w : GridWindow) : ℕ :=
  w.width + w.height + w.cells + w.boundary + w.slack

theorem cells_le_certificate (w : GridWindow) :
    w.cells ≤ w.certificate := by
  unfold GridWindow.certificate
  omega

def sampleGridWindow : GridWindow :=
  { width := 4, height := 3, cells := 12, boundary := 14, slack := 0 }

example : sampleGridWindow.ready := by
  norm_num [sampleGridWindow, GridWindow.ready, GridWindow.dimensionReady,
    GridWindow.cellControlled, GridWindow.boundaryControlled]


structure FiniteGridModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteGridModelsBudgetCertificate.controlled
    (c : FiniteGridModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteGridModelsBudgetCertificate.budgetControlled
    (c : FiniteGridModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteGridModelsBudgetCertificate.Ready
    (c : FiniteGridModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteGridModelsBudgetCertificate.size
    (c : FiniteGridModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteGridModels_budgetCertificate_le_size
    (c : FiniteGridModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteGridModelsBudgetCertificate :
    FiniteGridModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteGridModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteGridModelsBudgetCertificate.controlled,
      sampleFiniteGridModelsBudgetCertificate]
  · norm_num [FiniteGridModelsBudgetCertificate.budgetControlled,
      sampleFiniteGridModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteGridModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteGridModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteGridModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteGridModelsBudgetCertificate.controlled,
      sampleFiniteGridModelsBudgetCertificate]
  · norm_num [FiniteGridModelsBudgetCertificate.budgetControlled,
      sampleFiniteGridModelsBudgetCertificate]

example :
    sampleFiniteGridModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteGridModelsBudgetCertificate.size := by
  apply finiteGridModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteGridModelsBudgetCertificate.controlled,
      sampleFiniteGridModelsBudgetCertificate]
  · norm_num [FiniteGridModelsBudgetCertificate.budgetControlled,
      sampleFiniteGridModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteGridModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteGridModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteGridModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteGridModels
