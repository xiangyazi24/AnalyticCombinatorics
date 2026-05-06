import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite coloring models.

The record keeps only the finite budget data needed to state simple
coloring feasibility predicates.
-/

namespace AnalyticCombinatorics.AppA.FiniteColoringModels

structure ColoringData where
  vertices : ℕ
  colors : ℕ
  conflicts : ℕ
deriving DecidableEq, Repr

def paletteNonempty (d : ColoringData) : Prop :=
  0 < d.colors

def conflictsWithinPalette (d : ColoringData) : Prop :=
  d.conflicts ≤ d.vertices * d.colors

def coloringReady (d : ColoringData) : Prop :=
  paletteNonempty d ∧ conflictsWithinPalette d

def coloringBudget (d : ColoringData) : ℕ :=
  d.vertices + d.colors + d.conflicts

theorem coloringReady.palette {d : ColoringData} (h : coloringReady d) :
    paletteNonempty d ∧ conflictsWithinPalette d ∧ d.conflicts ≤ coloringBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold coloringBudget
  omega

theorem vertices_le_coloringBudget (d : ColoringData) :
    d.vertices ≤ coloringBudget d := by
  unfold coloringBudget
  omega

def sampleColoringData : ColoringData :=
  { vertices := 5, colors := 3, conflicts := 7 }

example : coloringReady sampleColoringData := by
  norm_num [coloringReady, paletteNonempty]
  norm_num [conflictsWithinPalette, sampleColoringData]

example : coloringBudget sampleColoringData = 15 := by
  native_decide

structure ColoringWindow where
  vertices : ℕ
  colors : ℕ
  conflicts : ℕ
  paletteChecks : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ColoringWindow.conflictsControlled (w : ColoringWindow) : Prop :=
  w.conflicts ≤ w.vertices * w.colors + w.slack

def ColoringWindow.paletteChecksControlled (w : ColoringWindow) : Prop :=
  w.paletteChecks ≤ w.vertices + w.colors + w.conflicts + w.slack

def coloringWindowReady (w : ColoringWindow) : Prop :=
  0 < w.colors ∧
    w.conflictsControlled ∧
    w.paletteChecksControlled

def ColoringWindow.certificate (w : ColoringWindow) : ℕ :=
  w.vertices + w.colors + w.conflicts + w.slack

theorem coloring_paletteChecks_le_certificate {w : ColoringWindow}
    (h : coloringWindowReady w) :
    w.paletteChecks ≤ w.certificate := by
  rcases h with ⟨_, _, hchecks⟩
  exact hchecks

def sampleColoringWindow : ColoringWindow :=
  { vertices := 5, colors := 3, conflicts := 7, paletteChecks := 14, slack := 0 }

example : coloringWindowReady sampleColoringWindow := by
  norm_num [coloringWindowReady, ColoringWindow.conflictsControlled,
    ColoringWindow.paletteChecksControlled, sampleColoringWindow]

example : sampleColoringWindow.certificate = 15 := by
  native_decide


structure FiniteColoringModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteColoringModelsBudgetCertificate.controlled
    (c : FiniteColoringModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteColoringModelsBudgetCertificate.budgetControlled
    (c : FiniteColoringModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteColoringModelsBudgetCertificate.Ready
    (c : FiniteColoringModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteColoringModelsBudgetCertificate.size
    (c : FiniteColoringModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteColoringModels_budgetCertificate_le_size
    (c : FiniteColoringModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteColoringModelsBudgetCertificate :
    FiniteColoringModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteColoringModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteColoringModelsBudgetCertificate.controlled,
      sampleFiniteColoringModelsBudgetCertificate]
  · norm_num [FiniteColoringModelsBudgetCertificate.budgetControlled,
      sampleFiniteColoringModelsBudgetCertificate]

example :
    sampleFiniteColoringModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteColoringModelsBudgetCertificate.size := by
  apply finiteColoringModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteColoringModelsBudgetCertificate.controlled,
      sampleFiniteColoringModelsBudgetCertificate]
  · norm_num [FiniteColoringModelsBudgetCertificate.budgetControlled,
      sampleFiniteColoringModelsBudgetCertificate]

/-- Finite executable readiness audit for finite-coloring certificates. -/
def finiteColoringModelsBudgetCertificateListReady
    (data : List FiniteColoringModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteColoringModelsBudgetCertificateList_readyWindow :
    finiteColoringModelsBudgetCertificateListReady
      [sampleFiniteColoringModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold finiteColoringModelsBudgetCertificateListReady
    sampleFiniteColoringModelsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteColoringModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteColoringModelsBudgetCertificate.controlled,
      sampleFiniteColoringModelsBudgetCertificate]
  · norm_num [FiniteColoringModelsBudgetCertificate.budgetControlled,
      sampleFiniteColoringModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteColoringModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteColoringModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FiniteColoringModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteColoringModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFiniteColoringModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FiniteColoringModels
