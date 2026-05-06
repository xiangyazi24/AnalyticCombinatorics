import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Montel-family bookkeeping models.

Normality is represented by local boundedness and finite compact-cover
budgets.
-/

namespace AnalyticCombinatorics.AppB.MontelModels

structure MontelDatum where
  compactCoverSize : ℕ
  localBound : ℕ
  extractionBudget : ℕ
deriving DecidableEq, Repr

def nonemptyCompactCover (d : MontelDatum) : Prop :=
  0 < d.compactCoverSize

def locallyBounded (d : MontelDatum) : Prop :=
  0 < d.localBound

def montelReady (d : MontelDatum) : Prop :=
  nonemptyCompactCover d ∧ locallyBounded d

def normalFamilyBudget (d : MontelDatum) : ℕ :=
  d.compactCoverSize * d.localBound + d.extractionBudget

theorem montelReady.bound {d : MontelDatum}
    (h : montelReady d) :
    nonemptyCompactCover d ∧ locallyBounded d ∧
      d.extractionBudget ≤ normalFamilyBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold normalFamilyBudget
  omega

theorem extractionBudget_le_normalFamilyBudget (d : MontelDatum) :
    d.extractionBudget ≤ normalFamilyBudget d := by
  unfold normalFamilyBudget
  omega

def sampleMontel : MontelDatum :=
  { compactCoverSize := 3, localBound := 4, extractionBudget := 2 }

example : montelReady sampleMontel := by
  norm_num [montelReady, nonemptyCompactCover, locallyBounded, sampleMontel]

example : normalFamilyBudget sampleMontel = 14 := by
  native_decide

structure MontelWindow where
  compactWindow : ℕ
  localBoundWindow : ℕ
  extractionWindow : ℕ
  normalBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MontelWindow.extractionControlled (w : MontelWindow) : Prop :=
  w.extractionWindow ≤ w.compactWindow * w.localBoundWindow + w.slack

def montelWindowReady (w : MontelWindow) : Prop :=
  0 < w.compactWindow ∧ 0 < w.localBoundWindow ∧ w.extractionControlled ∧
    w.normalBudget ≤ w.compactWindow * w.localBoundWindow + w.extractionWindow + w.slack

def MontelWindow.certificate (w : MontelWindow) : ℕ :=
  w.compactWindow * w.localBoundWindow + w.extractionWindow + w.normalBudget + w.slack

theorem montel_normalBudget_le_certificate (w : MontelWindow) :
    w.normalBudget ≤ w.certificate := by
  unfold MontelWindow.certificate
  omega

def sampleMontelWindow : MontelWindow :=
  { compactWindow := 3, localBoundWindow := 4, extractionWindow := 2,
    normalBudget := 15, slack := 1 }

example : montelWindowReady sampleMontelWindow := by
  norm_num [montelWindowReady, MontelWindow.extractionControlled, sampleMontelWindow]


structure MontelModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MontelModelsBudgetCertificate.controlled
    (c : MontelModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MontelModelsBudgetCertificate.budgetControlled
    (c : MontelModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MontelModelsBudgetCertificate.Ready
    (c : MontelModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MontelModelsBudgetCertificate.size
    (c : MontelModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem montelModels_budgetCertificate_le_size
    (c : MontelModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMontelModelsBudgetCertificate :
    MontelModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMontelModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [MontelModelsBudgetCertificate.controlled,
      sampleMontelModelsBudgetCertificate]
  · norm_num [MontelModelsBudgetCertificate.budgetControlled,
      sampleMontelModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMontelModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleMontelModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMontelModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [MontelModelsBudgetCertificate.controlled,
      sampleMontelModelsBudgetCertificate]
  · norm_num [MontelModelsBudgetCertificate.budgetControlled,
      sampleMontelModelsBudgetCertificate]

example :
    sampleMontelModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleMontelModelsBudgetCertificate.size := by
  apply montelModels_budgetCertificate_le_size
  constructor
  · norm_num [MontelModelsBudgetCertificate.controlled,
      sampleMontelModelsBudgetCertificate]
  · norm_num [MontelModelsBudgetCertificate.budgetControlled,
      sampleMontelModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MontelModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMontelModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMontelModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.MontelModels
