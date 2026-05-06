import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite substitution models.

The finite schema records outer slots, inner objects, and compatibility
slack for substitution constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteSubstitutionModels

structure SubstitutionData where
  outerSlots : ℕ
  innerObjects : ℕ
  compatibilitySlack : ℕ
deriving DecidableEq, Repr

def outerSlotsPositive (d : SubstitutionData) : Prop :=
  0 < d.outerSlots

def innerObjectsControlled (d : SubstitutionData) : Prop :=
  d.innerObjects ≤ d.outerSlots + d.compatibilitySlack

def substitutionReady (d : SubstitutionData) : Prop :=
  outerSlotsPositive d ∧ innerObjectsControlled d

def substitutionBudget (d : SubstitutionData) : ℕ :=
  d.outerSlots + d.innerObjects + d.compatibilitySlack

theorem substitutionReady.outer {d : SubstitutionData}
    (h : substitutionReady d) :
    outerSlotsPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem innerObjects_le_substitutionBudget (d : SubstitutionData) :
    d.innerObjects ≤ substitutionBudget d := by
  unfold substitutionBudget
  omega

def sampleSubstitutionData : SubstitutionData :=
  { outerSlots := 6, innerObjects := 8, compatibilitySlack := 3 }

example : substitutionReady sampleSubstitutionData := by
  norm_num [substitutionReady, outerSlotsPositive]
  norm_num [innerObjectsControlled, sampleSubstitutionData]

example : substitutionBudget sampleSubstitutionData = 17 := by
  native_decide

structure SubstitutionWindow where
  outerSlots : ℕ
  innerObjects : ℕ
  compatibilitySlack : ℕ
  substitutionMapBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubstitutionWindow.innerControlled (w : SubstitutionWindow) : Prop :=
  w.innerObjects ≤ w.outerSlots + w.compatibilitySlack + w.slack

def SubstitutionWindow.mapControlled (w : SubstitutionWindow) : Prop :=
  w.substitutionMapBudget ≤ w.outerSlots + w.innerObjects + w.compatibilitySlack + w.slack

def substitutionWindowReady (w : SubstitutionWindow) : Prop :=
  0 < w.outerSlots ∧
    w.innerControlled ∧
    w.mapControlled

def SubstitutionWindow.certificate (w : SubstitutionWindow) : ℕ :=
  w.outerSlots + w.innerObjects + w.compatibilitySlack + w.slack

theorem substitution_mapBudget_le_certificate {w : SubstitutionWindow}
    (h : substitutionWindowReady w) :
    w.substitutionMapBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hmap⟩
  exact hmap

def sampleSubstitutionWindow : SubstitutionWindow :=
  { outerSlots := 6, innerObjects := 8, compatibilitySlack := 3, substitutionMapBudget := 16,
    slack := 0 }

example : substitutionWindowReady sampleSubstitutionWindow := by
  norm_num [substitutionWindowReady, SubstitutionWindow.innerControlled,
    SubstitutionWindow.mapControlled, sampleSubstitutionWindow]

example : sampleSubstitutionWindow.certificate = 17 := by
  native_decide


structure FiniteSubstitutionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSubstitutionModelsBudgetCertificate.controlled
    (c : FiniteSubstitutionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSubstitutionModelsBudgetCertificate.budgetControlled
    (c : FiniteSubstitutionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSubstitutionModelsBudgetCertificate.Ready
    (c : FiniteSubstitutionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSubstitutionModelsBudgetCertificate.size
    (c : FiniteSubstitutionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSubstitutionModels_budgetCertificate_le_size
    (c : FiniteSubstitutionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSubstitutionModelsBudgetCertificate :
    FiniteSubstitutionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSubstitutionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSubstitutionModelsBudgetCertificate.controlled,
      sampleFiniteSubstitutionModelsBudgetCertificate]
  · norm_num [FiniteSubstitutionModelsBudgetCertificate.budgetControlled,
      sampleFiniteSubstitutionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSubstitutionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSubstitutionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSubstitutionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSubstitutionModelsBudgetCertificate.controlled,
      sampleFiniteSubstitutionModelsBudgetCertificate]
  · norm_num [FiniteSubstitutionModelsBudgetCertificate.budgetControlled,
      sampleFiniteSubstitutionModelsBudgetCertificate]

example :
    sampleFiniteSubstitutionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSubstitutionModelsBudgetCertificate.size := by
  apply finiteSubstitutionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSubstitutionModelsBudgetCertificate.controlled,
      sampleFiniteSubstitutionModelsBudgetCertificate]
  · norm_num [FiniteSubstitutionModelsBudgetCertificate.budgetControlled,
      sampleFiniteSubstitutionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteSubstitutionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSubstitutionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSubstitutionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSubstitutionModels
