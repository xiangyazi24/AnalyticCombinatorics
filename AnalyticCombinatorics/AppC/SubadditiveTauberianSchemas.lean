import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Subadditive Tauberian schema bookkeeping.

The finite record stores subadditivity, normalization, and error budgets.
-/

namespace AnalyticCombinatorics.AppC.SubadditiveTauberianSchemas

structure SubadditiveDatum where
  firstBudget : ℕ
  secondBudget : ℕ
  combinedBudget : ℕ
deriving DecidableEq, Repr

def subadditiveBound (d : SubadditiveDatum) : Prop :=
  d.combinedBudget ≤ d.firstBudget + d.secondBudget

def positiveNormalization (d : SubadditiveDatum) : Prop :=
  0 < d.firstBudget + d.secondBudget

def subadditiveTauberianReady (d : SubadditiveDatum) : Prop :=
  subadditiveBound d ∧ positiveNormalization d

def subadditiveSlack (d : SubadditiveDatum) : ℕ :=
  d.firstBudget + d.secondBudget - d.combinedBudget

theorem subadditiveTauberianReady.bound {d : SubadditiveDatum}
    (h : subadditiveTauberianReady d) :
    subadditiveBound d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem subadditiveSlack_add {d : SubadditiveDatum}
    (h : subadditiveBound d) :
    subadditiveSlack d + d.combinedBudget = d.firstBudget + d.secondBudget := by
  unfold subadditiveSlack subadditiveBound at *
  omega

def sampleSubadditive : SubadditiveDatum :=
  { firstBudget := 6, secondBudget := 5, combinedBudget := 9 }

example : subadditiveTauberianReady sampleSubadditive := by
  norm_num [subadditiveTauberianReady, subadditiveBound, positiveNormalization, sampleSubadditive]

example : subadditiveSlack sampleSubadditive = 2 := by
  native_decide

structure SubadditiveWindow where
  firstBudget : ℕ
  secondBudget : ℕ
  combinedBudget : ℕ
  normalizationBudget : ℕ
deriving DecidableEq, Repr

def SubadditiveWindow.boundReady (w : SubadditiveWindow) : Prop :=
  w.combinedBudget ≤ w.firstBudget + w.secondBudget

def SubadditiveWindow.normalizationReady (w : SubadditiveWindow) : Prop :=
  0 < w.firstBudget + w.secondBudget + w.normalizationBudget

def SubadditiveWindow.ready (w : SubadditiveWindow) : Prop :=
  w.boundReady ∧ w.normalizationReady

def SubadditiveWindow.certificate (w : SubadditiveWindow) : ℕ :=
  w.firstBudget + w.secondBudget + w.combinedBudget + w.normalizationBudget

theorem combinedBudget_le_certificate (w : SubadditiveWindow) :
    w.combinedBudget ≤ w.certificate := by
  unfold SubadditiveWindow.certificate
  omega

def sampleSubadditiveWindow : SubadditiveWindow :=
  { firstBudget := 6, secondBudget := 5, combinedBudget := 9, normalizationBudget := 1 }

example : sampleSubadditiveWindow.ready := by
  norm_num [sampleSubadditiveWindow, SubadditiveWindow.ready,
    SubadditiveWindow.boundReady, SubadditiveWindow.normalizationReady]

structure SubadditiveRefinementWindow where
  firstWindow : ℕ
  secondWindow : ℕ
  combinedWindow : ℕ
  subadditiveBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubadditiveRefinementWindow.boundControlled
    (w : SubadditiveRefinementWindow) : Prop :=
  w.combinedWindow ≤ w.firstWindow + w.secondWindow + w.slack

def subadditiveRefinementWindowReady
    (w : SubadditiveRefinementWindow) : Prop :=
  w.boundControlled ∧
    w.subadditiveBudget ≤ w.firstWindow + w.secondWindow + w.combinedWindow + w.slack

def SubadditiveRefinementWindow.certificate
    (w : SubadditiveRefinementWindow) : ℕ :=
  w.firstWindow + w.secondWindow + w.combinedWindow + w.subadditiveBudget + w.slack

theorem subadditiveRefinement_budget_le_certificate
    (w : SubadditiveRefinementWindow) :
    w.subadditiveBudget ≤ w.certificate := by
  unfold SubadditiveRefinementWindow.certificate
  omega

def sampleSubadditiveRefinementWindow : SubadditiveRefinementWindow :=
  { firstWindow := 6, secondWindow := 5, combinedWindow := 9,
    subadditiveBudget := 21, slack := 1 }

example : subadditiveRefinementWindowReady
    sampleSubadditiveRefinementWindow := by
  norm_num [subadditiveRefinementWindowReady,
    SubadditiveRefinementWindow.boundControlled, sampleSubadditiveRefinementWindow]


structure SubadditiveTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubadditiveTauberianSchemasBudgetCertificate.controlled
    (c : SubadditiveTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SubadditiveTauberianSchemasBudgetCertificate.budgetControlled
    (c : SubadditiveTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SubadditiveTauberianSchemasBudgetCertificate.Ready
    (c : SubadditiveTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SubadditiveTauberianSchemasBudgetCertificate.size
    (c : SubadditiveTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem subadditiveTauberianSchemas_budgetCertificate_le_size
    (c : SubadditiveTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSubadditiveTauberianSchemasBudgetCertificate :
    SubadditiveTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSubadditiveTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SubadditiveTauberianSchemasBudgetCertificate.controlled,
      sampleSubadditiveTauberianSchemasBudgetCertificate]
  · norm_num [SubadditiveTauberianSchemasBudgetCertificate.budgetControlled,
      sampleSubadditiveTauberianSchemasBudgetCertificate]

example :
    sampleSubadditiveTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSubadditiveTauberianSchemasBudgetCertificate.size := by
  apply subadditiveTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [SubadditiveTauberianSchemasBudgetCertificate.controlled,
      sampleSubadditiveTauberianSchemasBudgetCertificate]
  · norm_num [SubadditiveTauberianSchemasBudgetCertificate.budgetControlled,
      sampleSubadditiveTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSubadditiveTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SubadditiveTauberianSchemasBudgetCertificate.controlled,
      sampleSubadditiveTauberianSchemasBudgetCertificate]
  · norm_num [SubadditiveTauberianSchemasBudgetCertificate.budgetControlled,
      sampleSubadditiveTauberianSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSubadditiveTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSubadditiveTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SubadditiveTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSubadditiveTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSubadditiveTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.SubadditiveTauberianSchemas
