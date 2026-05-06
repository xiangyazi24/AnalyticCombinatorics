import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite unlabelled construction models.

The finite schema records object classes, symmetry budget, and orbit
slack for unlabelled constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteUnlabelledConstructionModels

structure UnlabelledConstructionData where
  classCount : ℕ
  symmetryBudget : ℕ
  orbitSlack : ℕ
deriving DecidableEq, Repr

def classCountPositive (d : UnlabelledConstructionData) : Prop :=
  0 < d.classCount

def symmetryControlled (d : UnlabelledConstructionData) : Prop :=
  d.symmetryBudget ≤ d.classCount + d.orbitSlack

def unlabelledConstructionReady (d : UnlabelledConstructionData) : Prop :=
  classCountPositive d ∧ symmetryControlled d

def unlabelledConstructionBudget (d : UnlabelledConstructionData) : ℕ :=
  d.classCount + d.symmetryBudget + d.orbitSlack

theorem unlabelledConstructionReady.classes
    {d : UnlabelledConstructionData}
    (h : unlabelledConstructionReady d) :
    classCountPositive d ∧ symmetryControlled d ∧
      d.symmetryBudget ≤ unlabelledConstructionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold unlabelledConstructionBudget
  omega

theorem symmetryBudget_le_unlabelledBudget
    (d : UnlabelledConstructionData) :
    d.symmetryBudget ≤ unlabelledConstructionBudget d := by
  unfold unlabelledConstructionBudget
  omega

def sampleUnlabelledConstructionData : UnlabelledConstructionData :=
  { classCount := 6, symmetryBudget := 8, orbitSlack := 3 }

example : unlabelledConstructionReady sampleUnlabelledConstructionData := by
  norm_num [unlabelledConstructionReady, classCountPositive]
  norm_num [symmetryControlled, sampleUnlabelledConstructionData]

example : unlabelledConstructionBudget sampleUnlabelledConstructionData = 17 := by
  native_decide


structure FiniteUnlabelledConstructionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteUnlabelledConstructionModelsBudgetCertificate.controlled
    (c : FiniteUnlabelledConstructionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteUnlabelledConstructionModelsBudgetCertificate.budgetControlled
    (c : FiniteUnlabelledConstructionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteUnlabelledConstructionModelsBudgetCertificate.Ready
    (c : FiniteUnlabelledConstructionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteUnlabelledConstructionModelsBudgetCertificate.size
    (c : FiniteUnlabelledConstructionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteUnlabelledConstructionModels_budgetCertificate_le_size
    (c : FiniteUnlabelledConstructionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteUnlabelledConstructionModelsBudgetCertificate :
    FiniteUnlabelledConstructionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteUnlabelledConstructionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteUnlabelledConstructionModelsBudgetCertificate.controlled,
      sampleFiniteUnlabelledConstructionModelsBudgetCertificate]
  · norm_num [FiniteUnlabelledConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteUnlabelledConstructionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteUnlabelledConstructionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteUnlabelledConstructionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteUnlabelledConstructionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteUnlabelledConstructionModelsBudgetCertificate.controlled,
      sampleFiniteUnlabelledConstructionModelsBudgetCertificate]
  · norm_num [FiniteUnlabelledConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteUnlabelledConstructionModelsBudgetCertificate]

example :
    sampleFiniteUnlabelledConstructionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteUnlabelledConstructionModelsBudgetCertificate.size := by
  apply finiteUnlabelledConstructionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteUnlabelledConstructionModelsBudgetCertificate.controlled,
      sampleFiniteUnlabelledConstructionModelsBudgetCertificate]
  · norm_num [FiniteUnlabelledConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteUnlabelledConstructionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteUnlabelledConstructionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteUnlabelledConstructionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteUnlabelledConstructionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteUnlabelledConstructionModels
