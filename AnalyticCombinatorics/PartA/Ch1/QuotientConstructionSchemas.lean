import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Quotient construction schemas.

The finite schema tracks objects, equivalence classes, and orbit slack
for quotient constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.QuotientConstructionSchemas

structure QuotientConstructionData where
  objectCount : ℕ
  classCount : ℕ
  orbitSlack : ℕ
deriving DecidableEq, Repr

def quotientObjectsNonempty (d : QuotientConstructionData) : Prop :=
  0 < d.objectCount

def classesControlled (d : QuotientConstructionData) : Prop :=
  d.classCount ≤ d.objectCount + d.orbitSlack

def quotientConstructionReady (d : QuotientConstructionData) : Prop :=
  quotientObjectsNonempty d ∧ classesControlled d

def quotientConstructionBudget (d : QuotientConstructionData) : ℕ :=
  d.objectCount + d.classCount + d.orbitSlack

theorem quotientConstructionReady.objects
    {d : QuotientConstructionData}
    (h : quotientConstructionReady d) :
    quotientObjectsNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem classCount_le_quotientBudget (d : QuotientConstructionData) :
    d.classCount ≤ quotientConstructionBudget d := by
  unfold quotientConstructionBudget
  omega

def sampleQuotientConstructionData : QuotientConstructionData :=
  { objectCount := 8, classCount := 5, orbitSlack := 2 }

example : quotientConstructionReady sampleQuotientConstructionData := by
  norm_num [quotientConstructionReady, quotientObjectsNonempty]
  norm_num [classesControlled, sampleQuotientConstructionData]

example : quotientConstructionBudget sampleQuotientConstructionData = 15 := by
  native_decide

structure QuotientConstructionBudgetCertificate where
  objectWindow : ℕ
  classWindow : ℕ
  orbitSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuotientConstructionBudgetCertificate.controlled
    (c : QuotientConstructionBudgetCertificate) : Prop :=
  0 < c.objectWindow ∧
    c.classWindow ≤ c.objectWindow + c.orbitSlackWindow + c.slack

def QuotientConstructionBudgetCertificate.budgetControlled
    (c : QuotientConstructionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.objectWindow + c.classWindow + c.orbitSlackWindow + c.slack

def QuotientConstructionBudgetCertificate.Ready
    (c : QuotientConstructionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def QuotientConstructionBudgetCertificate.size
    (c : QuotientConstructionBudgetCertificate) : ℕ :=
  c.objectWindow + c.classWindow + c.orbitSlackWindow + c.slack

theorem quotientConstruction_budgetCertificate_le_size
    (c : QuotientConstructionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleQuotientConstructionBudgetCertificate :
    QuotientConstructionBudgetCertificate :=
  { objectWindow := 8
    classWindow := 5
    orbitSlackWindow := 2
    certificateBudgetWindow := 16
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleQuotientConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [QuotientConstructionBudgetCertificate.controlled,
      sampleQuotientConstructionBudgetCertificate]
  · norm_num [QuotientConstructionBudgetCertificate.budgetControlled,
      sampleQuotientConstructionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleQuotientConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleQuotientConstructionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleQuotientConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [QuotientConstructionBudgetCertificate.controlled,
      sampleQuotientConstructionBudgetCertificate]
  · norm_num [QuotientConstructionBudgetCertificate.budgetControlled,
      sampleQuotientConstructionBudgetCertificate]

example :
    sampleQuotientConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleQuotientConstructionBudgetCertificate.size := by
  apply quotientConstruction_budgetCertificate_le_size
  constructor
  · norm_num [QuotientConstructionBudgetCertificate.controlled,
      sampleQuotientConstructionBudgetCertificate]
  · norm_num [QuotientConstructionBudgetCertificate.budgetControlled,
      sampleQuotientConstructionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List QuotientConstructionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleQuotientConstructionBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleQuotientConstructionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.QuotientConstructionSchemas
