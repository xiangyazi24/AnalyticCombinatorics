import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Pole-free region bookkeeping.

The finite data records a protected radius, excluded pole count, and margin
budget.
-/

namespace AnalyticCombinatorics.AppB.PoleFreeRegionModels

structure PoleFreeDatum where
  protectedRadius : ℕ
  excludedPoleCount : ℕ
  marginBudget : ℕ
deriving DecidableEq, Repr

def positiveProtectedRadius (d : PoleFreeDatum) : Prop :=
  0 < d.protectedRadius

def noExcludedPoles (d : PoleFreeDatum) : Prop :=
  d.excludedPoleCount = 0

def poleFreeReady (d : PoleFreeDatum) : Prop :=
  positiveProtectedRadius d ∧ noExcludedPoles d

def poleFreeBudget (d : PoleFreeDatum) : ℕ :=
  d.protectedRadius + d.excludedPoleCount + d.marginBudget

theorem poleFreeReady.radius {d : PoleFreeDatum}
    (h : poleFreeReady d) :
    positiveProtectedRadius d ∧ noExcludedPoles d ∧
      d.protectedRadius ≤ poleFreeBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold poleFreeBudget
  omega

theorem protectedRadius_le_budget (d : PoleFreeDatum) :
    d.protectedRadius ≤ poleFreeBudget d := by
  unfold poleFreeBudget
  omega

def samplePoleFree : PoleFreeDatum :=
  { protectedRadius := 5, excludedPoleCount := 0, marginBudget := 3 }

example : poleFreeReady samplePoleFree := by
  norm_num [poleFreeReady, positiveProtectedRadius, noExcludedPoles, samplePoleFree]

example : poleFreeBudget samplePoleFree = 8 := by
  native_decide

structure PoleFreeWindow where
  protectedWindow : ℕ
  excludedWindow : ℕ
  marginWindow : ℕ
  regionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoleFreeWindow.exclusionsControlled (w : PoleFreeWindow) : Prop :=
  w.excludedWindow ≤ w.slack

def poleFreeWindowReady (w : PoleFreeWindow) : Prop :=
  0 < w.protectedWindow ∧ w.exclusionsControlled ∧
    w.regionBudget ≤ w.protectedWindow + w.marginWindow + w.slack

def PoleFreeWindow.certificate (w : PoleFreeWindow) : ℕ :=
  w.protectedWindow + w.excludedWindow + w.marginWindow + w.regionBudget + w.slack

theorem poleFree_regionBudget_le_certificate (w : PoleFreeWindow) :
    w.regionBudget ≤ w.certificate := by
  unfold PoleFreeWindow.certificate
  omega

def samplePoleFreeWindow : PoleFreeWindow :=
  { protectedWindow := 5, excludedWindow := 0, marginWindow := 3, regionBudget := 9, slack := 1 }

example : poleFreeWindowReady samplePoleFreeWindow := by
  norm_num [poleFreeWindowReady, PoleFreeWindow.exclusionsControlled, samplePoleFreeWindow]


structure PoleFreeRegionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoleFreeRegionModelsBudgetCertificate.controlled
    (c : PoleFreeRegionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PoleFreeRegionModelsBudgetCertificate.budgetControlled
    (c : PoleFreeRegionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PoleFreeRegionModelsBudgetCertificate.Ready
    (c : PoleFreeRegionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PoleFreeRegionModelsBudgetCertificate.size
    (c : PoleFreeRegionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem poleFreeRegionModels_budgetCertificate_le_size
    (c : PoleFreeRegionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePoleFreeRegionModelsBudgetCertificate :
    PoleFreeRegionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePoleFreeRegionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [PoleFreeRegionModelsBudgetCertificate.controlled,
      samplePoleFreeRegionModelsBudgetCertificate]
  · norm_num [PoleFreeRegionModelsBudgetCertificate.budgetControlled,
      samplePoleFreeRegionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePoleFreeRegionModelsBudgetCertificate.certificateBudgetWindow ≤
      samplePoleFreeRegionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePoleFreeRegionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [PoleFreeRegionModelsBudgetCertificate.controlled,
      samplePoleFreeRegionModelsBudgetCertificate]
  · norm_num [PoleFreeRegionModelsBudgetCertificate.budgetControlled,
      samplePoleFreeRegionModelsBudgetCertificate]

example :
    samplePoleFreeRegionModelsBudgetCertificate.certificateBudgetWindow ≤
      samplePoleFreeRegionModelsBudgetCertificate.size := by
  apply poleFreeRegionModels_budgetCertificate_le_size
  constructor
  · norm_num [PoleFreeRegionModelsBudgetCertificate.controlled,
      samplePoleFreeRegionModelsBudgetCertificate]
  · norm_num [PoleFreeRegionModelsBudgetCertificate.budgetControlled,
      samplePoleFreeRegionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PoleFreeRegionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePoleFreeRegionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePoleFreeRegionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.PoleFreeRegionModels
