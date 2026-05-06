import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Zero-free strip models.

The finite schema tracks strip width, zero-exclusion radius, and boundary
budget.
-/

namespace AnalyticCombinatorics.AppB.ZeroFreeStripModels

structure ZeroFreeStripData where
  stripWidth : ℕ
  exclusionRadius : ℕ
  boundaryBudget : ℕ
deriving DecidableEq, Repr

def stripWidthPositive (d : ZeroFreeStripData) : Prop :=
  0 < d.stripWidth

def exclusionControlled (d : ZeroFreeStripData) : Prop :=
  d.exclusionRadius ≤ d.stripWidth + d.boundaryBudget

def zeroFreeStripReady (d : ZeroFreeStripData) : Prop :=
  stripWidthPositive d ∧ exclusionControlled d

def zeroFreeStripBudget (d : ZeroFreeStripData) : ℕ :=
  d.stripWidth + d.exclusionRadius + d.boundaryBudget

theorem zeroFreeStripReady.width {d : ZeroFreeStripData}
    (h : zeroFreeStripReady d) :
    stripWidthPositive d ∧ exclusionControlled d ∧
      d.exclusionRadius ≤ zeroFreeStripBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold zeroFreeStripBudget
  omega

theorem exclusionRadius_le_zeroFreeBudget (d : ZeroFreeStripData) :
    d.exclusionRadius ≤ zeroFreeStripBudget d := by
  unfold zeroFreeStripBudget
  omega

def sampleZeroFreeStripData : ZeroFreeStripData :=
  { stripWidth := 6, exclusionRadius := 8, boundaryBudget := 3 }

example : zeroFreeStripReady sampleZeroFreeStripData := by
  norm_num [zeroFreeStripReady, stripWidthPositive]
  norm_num [exclusionControlled, sampleZeroFreeStripData]

example : zeroFreeStripBudget sampleZeroFreeStripData = 17 := by
  native_decide

/-- Finite executable readiness audit for zero-free strip data. -/
def zeroFreeStripListReady (windows : List ZeroFreeStripData) : Bool :=
  windows.all fun d =>
    0 < d.stripWidth && d.exclusionRadius ≤ d.stripWidth + d.boundaryBudget

theorem zeroFreeStripList_readyWindow :
    zeroFreeStripListReady
      [{ stripWidth := 4, exclusionRadius := 5, boundaryBudget := 1 },
       { stripWidth := 6, exclusionRadius := 8, boundaryBudget := 3 }] = true := by
  unfold zeroFreeStripListReady
  native_decide


structure ZeroFreeStripModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ZeroFreeStripModelsBudgetCertificate.controlled
    (c : ZeroFreeStripModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ZeroFreeStripModelsBudgetCertificate.budgetControlled
    (c : ZeroFreeStripModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ZeroFreeStripModelsBudgetCertificate.Ready
    (c : ZeroFreeStripModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ZeroFreeStripModelsBudgetCertificate.size
    (c : ZeroFreeStripModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem zeroFreeStripModels_budgetCertificate_le_size
    (c : ZeroFreeStripModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleZeroFreeStripModelsBudgetCertificate :
    ZeroFreeStripModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleZeroFreeStripModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [ZeroFreeStripModelsBudgetCertificate.controlled,
      sampleZeroFreeStripModelsBudgetCertificate]
  · norm_num [ZeroFreeStripModelsBudgetCertificate.budgetControlled,
      sampleZeroFreeStripModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleZeroFreeStripModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleZeroFreeStripModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleZeroFreeStripModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [ZeroFreeStripModelsBudgetCertificate.controlled,
      sampleZeroFreeStripModelsBudgetCertificate]
  · norm_num [ZeroFreeStripModelsBudgetCertificate.budgetControlled,
      sampleZeroFreeStripModelsBudgetCertificate]

example :
    sampleZeroFreeStripModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleZeroFreeStripModelsBudgetCertificate.size := by
  apply zeroFreeStripModels_budgetCertificate_le_size
  constructor
  · norm_num [ZeroFreeStripModelsBudgetCertificate.controlled,
      sampleZeroFreeStripModelsBudgetCertificate]
  · norm_num [ZeroFreeStripModelsBudgetCertificate.budgetControlled,
      sampleZeroFreeStripModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List ZeroFreeStripModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleZeroFreeStripModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleZeroFreeStripModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.ZeroFreeStripModels
