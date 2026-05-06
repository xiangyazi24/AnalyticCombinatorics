import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic slit domain models.

This module records finite bookkeeping for slit domain decompositions.
-/

namespace AnalyticCombinatorics.AppB.AnalyticSlitDomainModels

structure SlitDomainData where
  slitCount : ℕ
  domainPatches : ℕ
  slitSlack : ℕ
deriving DecidableEq, Repr

def hasSlitCount (d : SlitDomainData) : Prop :=
  0 < d.slitCount

def domainPatchesControlled (d : SlitDomainData) : Prop :=
  d.domainPatches ≤ d.slitCount + d.slitSlack

def slitDomainReady (d : SlitDomainData) : Prop :=
  hasSlitCount d ∧ domainPatchesControlled d

def slitDomainBudget (d : SlitDomainData) : ℕ :=
  d.slitCount + d.domainPatches + d.slitSlack

theorem slitDomainReady.hasSlitCount {d : SlitDomainData}
    (h : slitDomainReady d) :
    hasSlitCount d ∧ domainPatchesControlled d ∧
      d.domainPatches ≤ slitDomainBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold slitDomainBudget
  omega

theorem domainPatches_le_budget (d : SlitDomainData) :
    d.domainPatches ≤ slitDomainBudget d := by
  unfold slitDomainBudget
  omega

def sampleSlitDomainData : SlitDomainData :=
  { slitCount := 6, domainPatches := 8, slitSlack := 3 }

example : slitDomainReady sampleSlitDomainData := by
  norm_num [slitDomainReady, hasSlitCount]
  norm_num [domainPatchesControlled, sampleSlitDomainData]

example : slitDomainBudget sampleSlitDomainData = 17 := by
  native_decide

structure SlitDomainWindow where
  slitWindow : ℕ
  patchWindow : ℕ
  slitSlack : ℕ
  domainBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SlitDomainWindow.patchesControlled (w : SlitDomainWindow) : Prop :=
  w.patchWindow ≤ w.slitWindow + w.slitSlack + w.slack

def slitDomainWindowReady (w : SlitDomainWindow) : Prop :=
  0 < w.slitWindow ∧ w.patchesControlled ∧
    w.domainBudget ≤ w.slitWindow + w.patchWindow + w.slack

def SlitDomainWindow.certificate (w : SlitDomainWindow) : ℕ :=
  w.slitWindow + w.patchWindow + w.slitSlack + w.domainBudget + w.slack

theorem slitDomain_domainBudget_le_certificate (w : SlitDomainWindow) :
    w.domainBudget ≤ w.certificate := by
  unfold SlitDomainWindow.certificate
  omega

def sampleSlitDomainWindow : SlitDomainWindow :=
  { slitWindow := 5, patchWindow := 7, slitSlack := 2, domainBudget := 14, slack := 2 }

example : slitDomainWindowReady sampleSlitDomainWindow := by
  norm_num [slitDomainWindowReady, SlitDomainWindow.patchesControlled, sampleSlitDomainWindow]


structure AnalyticSlitDomainModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticSlitDomainModelsBudgetCertificate.controlled
    (c : AnalyticSlitDomainModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticSlitDomainModelsBudgetCertificate.budgetControlled
    (c : AnalyticSlitDomainModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticSlitDomainModelsBudgetCertificate.Ready
    (c : AnalyticSlitDomainModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticSlitDomainModelsBudgetCertificate.size
    (c : AnalyticSlitDomainModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticSlitDomainModels_budgetCertificate_le_size
    (c : AnalyticSlitDomainModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticSlitDomainModelsBudgetCertificate :
    AnalyticSlitDomainModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticSlitDomainModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticSlitDomainModelsBudgetCertificate.controlled,
      sampleAnalyticSlitDomainModelsBudgetCertificate]
  · norm_num [AnalyticSlitDomainModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSlitDomainModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticSlitDomainModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticSlitDomainModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticSlitDomainModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticSlitDomainModelsBudgetCertificate.controlled,
      sampleAnalyticSlitDomainModelsBudgetCertificate]
  · norm_num [AnalyticSlitDomainModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSlitDomainModelsBudgetCertificate]

example :
    sampleAnalyticSlitDomainModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticSlitDomainModelsBudgetCertificate.size := by
  apply analyticSlitDomainModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticSlitDomainModelsBudgetCertificate.controlled,
      sampleAnalyticSlitDomainModelsBudgetCertificate]
  · norm_num [AnalyticSlitDomainModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSlitDomainModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticSlitDomainModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticSlitDomainModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticSlitDomainModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticSlitDomainModels
