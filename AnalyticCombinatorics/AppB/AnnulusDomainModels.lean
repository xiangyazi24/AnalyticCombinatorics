import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Annulus domain models.

The finite abstraction records inner radius, outer radius, and boundary
slack for annular domains.
-/

namespace AnalyticCombinatorics.AppB.AnnulusDomainModels

structure AnnulusDomainData where
  innerRadius : ℕ
  outerRadius : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def positiveInnerRadius (d : AnnulusDomainData) : Prop :=
  0 < d.innerRadius

def innerWithinOuter (d : AnnulusDomainData) : Prop :=
  d.innerRadius ≤ d.outerRadius

def annulusDomainReady (d : AnnulusDomainData) : Prop :=
  positiveInnerRadius d ∧ innerWithinOuter d

def annulusDomainBudget (d : AnnulusDomainData) : ℕ :=
  d.innerRadius + d.outerRadius + d.boundarySlack

theorem annulusDomainReady.inner {d : AnnulusDomainData}
    (h : annulusDomainReady d) :
    positiveInnerRadius d ∧ innerWithinOuter d ∧
      d.outerRadius ≤ annulusDomainBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold annulusDomainBudget
  omega

theorem outerRadius_le_annulusBudget (d : AnnulusDomainData) :
    d.outerRadius ≤ annulusDomainBudget d := by
  unfold annulusDomainBudget
  omega

def sampleAnnulusDomainData : AnnulusDomainData :=
  { innerRadius := 3, outerRadius := 9, boundarySlack := 2 }

example : annulusDomainReady sampleAnnulusDomainData := by
  norm_num [annulusDomainReady, positiveInnerRadius]
  norm_num [innerWithinOuter, sampleAnnulusDomainData]

example : annulusDomainBudget sampleAnnulusDomainData = 14 := by
  native_decide

/-- Finite executable readiness audit for annulus-domain windows. -/
def annulusDomainListReady (windows : List AnnulusDomainData) : Bool :=
  windows.all fun d => 0 < d.innerRadius && d.innerRadius ≤ d.outerRadius

theorem annulusDomainList_readyWindow :
    annulusDomainListReady
      [{ innerRadius := 1, outerRadius := 3, boundarySlack := 0 },
       { innerRadius := 3, outerRadius := 9, boundarySlack := 2 }] = true := by
  unfold annulusDomainListReady
  native_decide


structure AnnulusDomainModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnnulusDomainModelsBudgetCertificate.controlled
    (c : AnnulusDomainModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnnulusDomainModelsBudgetCertificate.budgetControlled
    (c : AnnulusDomainModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnnulusDomainModelsBudgetCertificate.Ready
    (c : AnnulusDomainModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnnulusDomainModelsBudgetCertificate.size
    (c : AnnulusDomainModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem annulusDomainModels_budgetCertificate_le_size
    (c : AnnulusDomainModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnnulusDomainModelsBudgetCertificate :
    AnnulusDomainModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnnulusDomainModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnnulusDomainModelsBudgetCertificate.controlled,
      sampleAnnulusDomainModelsBudgetCertificate]
  · norm_num [AnnulusDomainModelsBudgetCertificate.budgetControlled,
      sampleAnnulusDomainModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnnulusDomainModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnnulusDomainModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnnulusDomainModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnnulusDomainModelsBudgetCertificate.controlled,
      sampleAnnulusDomainModelsBudgetCertificate]
  · norm_num [AnnulusDomainModelsBudgetCertificate.budgetControlled,
      sampleAnnulusDomainModelsBudgetCertificate]

example :
    sampleAnnulusDomainModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnnulusDomainModelsBudgetCertificate.size := by
  apply annulusDomainModels_budgetCertificate_le_size
  constructor
  · norm_num [AnnulusDomainModelsBudgetCertificate.controlled,
      sampleAnnulusDomainModelsBudgetCertificate]
  · norm_num [AnnulusDomainModelsBudgetCertificate.budgetControlled,
      sampleAnnulusDomainModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnnulusDomainModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnnulusDomainModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnnulusDomainModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.AnnulusDomainModels
