import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Abelian limit schemas for nonnegative coefficient sequences.

This module records finite monotonicity and boundedness conditions that
serve as the coefficient-side input to Abelian limit statements.
-/

namespace AnalyticCombinatorics.AppC.AbelianLimitSchemas

structure AbelianData where
  partialBound : ℕ
  tailBound : ℕ
  monotone : Prop
deriving Repr

def boundedAbelianData (d : AbelianData) : Prop :=
  d.tailBound ≤ d.partialBound

def abelianReady (d : AbelianData) : Prop :=
  d.monotone ∧ boundedAbelianData d

def combinedBound (d : AbelianData) : ℕ :=
  d.partialBound + d.tailBound

theorem abelianReady.bound {d : AbelianData}
    (h : abelianReady d) :
    boundedAbelianData d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem combinedBound_ge_partial (d : AbelianData) :
    d.partialBound ≤ combinedBound d := by
  unfold combinedBound
  omega

def sampleAbelian : AbelianData :=
  { partialBound := 10, tailBound := 4, monotone := 4 ≤ 10 }

example : abelianReady sampleAbelian := by
  norm_num [abelianReady, boundedAbelianData, sampleAbelian]

example : combinedBound sampleAbelian = 14 := by
  native_decide

structure AbelianLimitWindow where
  cutoff : ℕ
  partialBound : ℕ
  tailBound : ℕ
  limitSlack : ℕ
deriving DecidableEq, Repr

def AbelianLimitWindow.tailControlled (w : AbelianLimitWindow) : Prop :=
  w.tailBound ≤ w.partialBound + w.limitSlack

def AbelianLimitWindow.nontrivialCutoff (w : AbelianLimitWindow) : Prop :=
  0 < w.cutoff

def AbelianLimitWindow.ready (w : AbelianLimitWindow) : Prop :=
  w.nontrivialCutoff ∧ w.tailControlled

def AbelianLimitWindow.certificate (w : AbelianLimitWindow) : ℕ :=
  w.cutoff + w.partialBound + w.tailBound + w.limitSlack

theorem tailBound_le_certificate (w : AbelianLimitWindow) :
    w.tailBound ≤ w.certificate := by
  unfold AbelianLimitWindow.certificate
  omega

def sampleAbelianLimitWindow : AbelianLimitWindow :=
  { cutoff := 5, partialBound := 10, tailBound := 4, limitSlack := 0 }

example : sampleAbelianLimitWindow.ready := by
  norm_num [sampleAbelianLimitWindow, AbelianLimitWindow.ready,
    AbelianLimitWindow.nontrivialCutoff, AbelianLimitWindow.tailControlled]

structure AbelianLimitRefinementWindow where
  cutoffWindow : ℕ
  partialWindow : ℕ
  tailWindow : ℕ
  abelianBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AbelianLimitRefinementWindow.tailControlled
    (w : AbelianLimitRefinementWindow) : Prop :=
  w.tailWindow ≤ w.partialWindow + w.slack

def abelianLimitRefinementWindowReady
    (w : AbelianLimitRefinementWindow) : Prop :=
  0 < w.cutoffWindow ∧ w.tailControlled ∧
    w.abelianBudget ≤ w.cutoffWindow + w.partialWindow + w.tailWindow + w.slack

def AbelianLimitRefinementWindow.certificate
    (w : AbelianLimitRefinementWindow) : ℕ :=
  w.cutoffWindow + w.partialWindow + w.tailWindow + w.abelianBudget + w.slack

theorem abelianLimitRefinement_budget_le_certificate
    (w : AbelianLimitRefinementWindow) :
    w.abelianBudget ≤ w.certificate := by
  unfold AbelianLimitRefinementWindow.certificate
  omega

def sampleAbelianLimitRefinementWindow : AbelianLimitRefinementWindow :=
  { cutoffWindow := 5, partialWindow := 10, tailWindow := 4,
    abelianBudget := 20, slack := 1 }

example : abelianLimitRefinementWindowReady
    sampleAbelianLimitRefinementWindow := by
  norm_num [abelianLimitRefinementWindowReady,
    AbelianLimitRefinementWindow.tailControlled, sampleAbelianLimitRefinementWindow]


structure AbelianLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AbelianLimitSchemasBudgetCertificate.controlled
    (c : AbelianLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AbelianLimitSchemasBudgetCertificate.budgetControlled
    (c : AbelianLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AbelianLimitSchemasBudgetCertificate.Ready
    (c : AbelianLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AbelianLimitSchemasBudgetCertificate.size
    (c : AbelianLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem abelianLimitSchemas_budgetCertificate_le_size
    (c : AbelianLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAbelianLimitSchemasBudgetCertificate :
    AbelianLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAbelianLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AbelianLimitSchemasBudgetCertificate.controlled,
      sampleAbelianLimitSchemasBudgetCertificate]
  · norm_num [AbelianLimitSchemasBudgetCertificate.budgetControlled,
      sampleAbelianLimitSchemasBudgetCertificate]

example :
    sampleAbelianLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAbelianLimitSchemasBudgetCertificate.size := by
  apply abelianLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [AbelianLimitSchemasBudgetCertificate.controlled,
      sampleAbelianLimitSchemasBudgetCertificate]
  · norm_num [AbelianLimitSchemasBudgetCertificate.budgetControlled,
      sampleAbelianLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAbelianLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AbelianLimitSchemasBudgetCertificate.controlled,
      sampleAbelianLimitSchemasBudgetCertificate]
  · norm_num [AbelianLimitSchemasBudgetCertificate.budgetControlled,
      sampleAbelianLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAbelianLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAbelianLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AbelianLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAbelianLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAbelianLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.AbelianLimitSchemas
