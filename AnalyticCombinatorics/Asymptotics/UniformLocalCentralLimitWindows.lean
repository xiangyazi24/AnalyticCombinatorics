import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform local central limit windows.

This module records finite bookkeeping for uniform local central limits.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformLocalCentralLimitWindows

structure LocalCentralLimitWindowData where
  varianceScale : ℕ
  latticeWindow : ℕ
  localSlack : ℕ
deriving DecidableEq, Repr

def hasVarianceScale (d : LocalCentralLimitWindowData) : Prop :=
  0 < d.varianceScale

def latticeWindowControlled (d : LocalCentralLimitWindowData) : Prop :=
  d.latticeWindow ≤ d.varianceScale + d.localSlack

def localCentralLimitReady (d : LocalCentralLimitWindowData) : Prop :=
  hasVarianceScale d ∧ latticeWindowControlled d

def localCentralLimitBudget (d : LocalCentralLimitWindowData) : ℕ :=
  d.varianceScale + d.latticeWindow + d.localSlack

theorem localCentralLimitReady.hasVarianceScale
    {d : LocalCentralLimitWindowData}
    (h : localCentralLimitReady d) :
    hasVarianceScale d ∧ latticeWindowControlled d ∧
      d.latticeWindow ≤ localCentralLimitBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold localCentralLimitBudget
  omega

theorem latticeWindow_le_budget (d : LocalCentralLimitWindowData) :
    d.latticeWindow ≤ localCentralLimitBudget d := by
  unfold localCentralLimitBudget
  omega

def sampleLocalCentralLimitWindowData : LocalCentralLimitWindowData :=
  { varianceScale := 6, latticeWindow := 8, localSlack := 3 }

example : localCentralLimitReady sampleLocalCentralLimitWindowData := by
  norm_num [localCentralLimitReady, hasVarianceScale]
  norm_num [latticeWindowControlled, sampleLocalCentralLimitWindowData]

example : localCentralLimitBudget sampleLocalCentralLimitWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for local central limit windows. -/
def localCentralLimitWindowDataListReady
    (data : List LocalCentralLimitWindowData) : Bool :=
  data.all fun d =>
    0 < d.varianceScale && d.latticeWindow ≤ d.varianceScale + d.localSlack

theorem localCentralLimitWindowDataList_readyWindow :
    localCentralLimitWindowDataListReady
      [{ varianceScale := 4, latticeWindow := 5, localSlack := 1 },
       { varianceScale := 6, latticeWindow := 8, localSlack := 3 }] = true := by
  unfold localCentralLimitWindowDataListReady
  native_decide

/-- A certificate window for uniform local central limits. -/
structure LocalCentralLimitCertificateWindow where
  varianceWindow : ℕ
  latticeWindow : ℕ
  localSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The lattice window is controlled by the variance window. -/
def localCentralLimitCertificateControlled
    (w : LocalCentralLimitCertificateWindow) : Prop :=
  w.latticeWindow ≤ w.varianceWindow + w.localSlack + w.slack

/-- Readiness for a local central limit certificate. -/
def localCentralLimitCertificateReady
    (w : LocalCentralLimitCertificateWindow) : Prop :=
  0 < w.varianceWindow ∧
    localCentralLimitCertificateControlled w ∧
      w.certificateBudget ≤ w.varianceWindow + w.latticeWindow + w.slack

/-- Total size of a local central limit certificate. -/
def localCentralLimitCertificate
    (w : LocalCentralLimitCertificateWindow) : ℕ :=
  w.varianceWindow + w.latticeWindow + w.localSlack + w.certificateBudget + w.slack

theorem localCentralLimitCertificate_budget_le_certificate
    (w : LocalCentralLimitCertificateWindow)
    (h : localCentralLimitCertificateReady w) :
    w.certificateBudget ≤ localCentralLimitCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold localCentralLimitCertificate
  omega

def sampleLocalCentralLimitCertificateWindow :
    LocalCentralLimitCertificateWindow where
  varianceWindow := 6
  latticeWindow := 7
  localSlack := 2
  certificateBudget := 12
  slack := 1

example :
    localCentralLimitCertificateReady
      sampleLocalCentralLimitCertificateWindow := by
  norm_num [localCentralLimitCertificateReady,
    localCentralLimitCertificateControlled,
    sampleLocalCentralLimitCertificateWindow]

example :
    sampleLocalCentralLimitCertificateWindow.certificateBudget ≤
      localCentralLimitCertificate sampleLocalCentralLimitCertificateWindow := by
  apply localCentralLimitCertificate_budget_le_certificate
  norm_num [localCentralLimitCertificateReady,
    localCentralLimitCertificateControlled,
    sampleLocalCentralLimitCertificateWindow]

structure LocalCentralLimitRefinementCertificate where
  varianceWindow : ℕ
  latticeWindow : ℕ
  localSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalCentralLimitRefinementCertificate.latticeControlled
    (c : LocalCentralLimitRefinementCertificate) : Prop :=
  c.latticeWindow ≤ c.varianceWindow + c.localSlackWindow + c.slack

def LocalCentralLimitRefinementCertificate.certificateBudgetControlled
    (c : LocalCentralLimitRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.varianceWindow + c.latticeWindow + c.localSlackWindow + c.slack

def localCentralLimitRefinementReady
    (c : LocalCentralLimitRefinementCertificate) : Prop :=
  0 < c.varianceWindow ∧ c.latticeControlled ∧ c.certificateBudgetControlled

def LocalCentralLimitRefinementCertificate.size
    (c : LocalCentralLimitRefinementCertificate) : ℕ :=
  c.varianceWindow + c.latticeWindow + c.localSlackWindow + c.slack

theorem localCentralLimit_certificateBudgetWindow_le_size
    {c : LocalCentralLimitRefinementCertificate}
    (h : localCentralLimitRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleLocalCentralLimitRefinementCertificate :
    LocalCentralLimitRefinementCertificate :=
  { varianceWindow := 6, latticeWindow := 7, localSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : localCentralLimitRefinementReady
    sampleLocalCentralLimitRefinementCertificate := by
  norm_num [localCentralLimitRefinementReady,
    LocalCentralLimitRefinementCertificate.latticeControlled,
    LocalCentralLimitRefinementCertificate.certificateBudgetControlled,
    sampleLocalCentralLimitRefinementCertificate]

example :
    sampleLocalCentralLimitRefinementCertificate.certificateBudgetWindow ≤
      sampleLocalCentralLimitRefinementCertificate.size := by
  norm_num [LocalCentralLimitRefinementCertificate.size,
    sampleLocalCentralLimitRefinementCertificate]

structure LocalCentralLimitBudgetCertificate where
  varianceWindow : ℕ
  latticeWindow : ℕ
  localSlackWindow : ℕ
  localBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalCentralLimitBudgetCertificate.controlled
    (c : LocalCentralLimitBudgetCertificate) : Prop :=
  0 < c.varianceWindow ∧
    c.latticeWindow ≤ c.varianceWindow + c.localSlackWindow + c.slack ∧
      c.localBudgetWindow ≤
        c.varianceWindow + c.latticeWindow + c.localSlackWindow + c.slack

def LocalCentralLimitBudgetCertificate.budgetControlled
    (c : LocalCentralLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.varianceWindow + c.latticeWindow + c.localSlackWindow +
      c.localBudgetWindow + c.slack

def LocalCentralLimitBudgetCertificate.Ready
    (c : LocalCentralLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LocalCentralLimitBudgetCertificate.size
    (c : LocalCentralLimitBudgetCertificate) : ℕ :=
  c.varianceWindow + c.latticeWindow + c.localSlackWindow +
    c.localBudgetWindow + c.slack

theorem localCentralLimit_budgetCertificate_le_size
    (c : LocalCentralLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLocalCentralLimitBudgetCertificate :
    LocalCentralLimitBudgetCertificate :=
  { varianceWindow := 6
    latticeWindow := 7
    localSlackWindow := 2
    localBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleLocalCentralLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalCentralLimitBudgetCertificate.controlled,
      sampleLocalCentralLimitBudgetCertificate]
  · norm_num [LocalCentralLimitBudgetCertificate.budgetControlled,
      sampleLocalCentralLimitBudgetCertificate]

example :
    sampleLocalCentralLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalCentralLimitBudgetCertificate.size := by
  apply localCentralLimit_budgetCertificate_le_size
  constructor
  · norm_num [LocalCentralLimitBudgetCertificate.controlled,
      sampleLocalCentralLimitBudgetCertificate]
  · norm_num [LocalCentralLimitBudgetCertificate.budgetControlled,
      sampleLocalCentralLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLocalCentralLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalCentralLimitBudgetCertificate.controlled,
      sampleLocalCentralLimitBudgetCertificate]
  · norm_num [LocalCentralLimitBudgetCertificate.budgetControlled,
      sampleLocalCentralLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLocalCentralLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalCentralLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LocalCentralLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLocalCentralLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLocalCentralLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformLocalCentralLimitWindows
