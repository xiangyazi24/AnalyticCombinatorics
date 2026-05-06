import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Substitution-schema coefficient bounds.

The module records finite outer/inner size budgets for subcritical and
critical substitution schemas.
-/

namespace AnalyticCombinatorics.PartB.Ch7.SubstitutionSchemaBounds

structure SubstitutionBound where
  outerSize : ℕ
  innerSize : ℕ
  compositionBudget : ℕ
deriving DecidableEq, Repr

def compositionSize (b : SubstitutionBound) : ℕ :=
  b.outerSize * b.innerSize

def substitutionControlled (b : SubstitutionBound) : Prop :=
  compositionSize b ≤ b.compositionBudget

def nontrivialSubstitution (b : SubstitutionBound) : Prop :=
  0 < b.outerSize ∧ 0 < b.innerSize

theorem substitutionControlled.size_le {b : SubstitutionBound}
    (h : substitutionControlled b) :
    substitutionControlled b ∧ compositionSize b ≤ b.compositionBudget := by
  exact ⟨h, h⟩

theorem compositionSize_positive {b : SubstitutionBound}
    (h : nontrivialSubstitution b) :
    0 < compositionSize b := by
  unfold compositionSize nontrivialSubstitution at *
  exact Nat.mul_pos h.1 h.2

def sampleSubstitution : SubstitutionBound :=
  { outerSize := 3, innerSize := 5, compositionBudget := 20 }

example : substitutionControlled sampleSubstitution := by
  norm_num [substitutionControlled, compositionSize, sampleSubstitution]

example : compositionSize sampleSubstitution = 15 := by
  native_decide

structure SubstitutionWindow where
  outerSize : ℕ
  innerSize : ℕ
  substitutedSize : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def SubstitutionWindow.nontrivial (w : SubstitutionWindow) : Prop :=
  0 < w.outerSize ∧ 0 < w.innerSize

def SubstitutionWindow.sizeControlled (w : SubstitutionWindow) : Prop :=
  w.substitutedSize ≤ w.outerSize * w.innerSize + w.errorSlack

def SubstitutionWindow.ready (w : SubstitutionWindow) : Prop :=
  w.nontrivial ∧ w.sizeControlled

def SubstitutionWindow.certificate (w : SubstitutionWindow) : ℕ :=
  w.outerSize + w.innerSize + w.substitutedSize + w.errorSlack

theorem substitutedSize_le_certificate (w : SubstitutionWindow) :
    w.substitutedSize ≤ w.certificate := by
  unfold SubstitutionWindow.certificate
  omega

def sampleSubstitutionWindow : SubstitutionWindow :=
  { outerSize := 3, innerSize := 5, substitutedSize := 15, errorSlack := 0 }

example : sampleSubstitutionWindow.ready := by
  norm_num [sampleSubstitutionWindow, SubstitutionWindow.ready,
    SubstitutionWindow.nontrivial, SubstitutionWindow.sizeControlled]


structure SubstitutionSchemaBoundsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubstitutionSchemaBoundsBudgetCertificate.controlled
    (c : SubstitutionSchemaBoundsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SubstitutionSchemaBoundsBudgetCertificate.budgetControlled
    (c : SubstitutionSchemaBoundsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SubstitutionSchemaBoundsBudgetCertificate.Ready
    (c : SubstitutionSchemaBoundsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SubstitutionSchemaBoundsBudgetCertificate.size
    (c : SubstitutionSchemaBoundsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem substitutionSchemaBounds_budgetCertificate_le_size
    (c : SubstitutionSchemaBoundsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSubstitutionSchemaBoundsBudgetCertificate :
    SubstitutionSchemaBoundsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSubstitutionSchemaBoundsBudgetCertificate.Ready := by
  constructor
  · norm_num [SubstitutionSchemaBoundsBudgetCertificate.controlled,
      sampleSubstitutionSchemaBoundsBudgetCertificate]
  · norm_num [SubstitutionSchemaBoundsBudgetCertificate.budgetControlled,
      sampleSubstitutionSchemaBoundsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSubstitutionSchemaBoundsBudgetCertificate.certificateBudgetWindow ≤
      sampleSubstitutionSchemaBoundsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSubstitutionSchemaBoundsBudgetCertificate.Ready := by
  constructor
  · norm_num [SubstitutionSchemaBoundsBudgetCertificate.controlled,
      sampleSubstitutionSchemaBoundsBudgetCertificate]
  · norm_num [SubstitutionSchemaBoundsBudgetCertificate.budgetControlled,
      sampleSubstitutionSchemaBoundsBudgetCertificate]

example :
    sampleSubstitutionSchemaBoundsBudgetCertificate.certificateBudgetWindow ≤
      sampleSubstitutionSchemaBoundsBudgetCertificate.size := by
  apply substitutionSchemaBounds_budgetCertificate_le_size
  constructor
  · norm_num [SubstitutionSchemaBoundsBudgetCertificate.controlled,
      sampleSubstitutionSchemaBoundsBudgetCertificate]
  · norm_num [SubstitutionSchemaBoundsBudgetCertificate.budgetControlled,
      sampleSubstitutionSchemaBoundsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SubstitutionSchemaBoundsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSubstitutionSchemaBoundsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSubstitutionSchemaBoundsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.SubstitutionSchemaBounds
