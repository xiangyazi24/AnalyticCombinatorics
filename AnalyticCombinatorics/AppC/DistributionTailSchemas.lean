import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Distribution tail schema bookkeeping.

The module records finite tail cutoffs and mass budgets for probability
limit laws.
-/

namespace AnalyticCombinatorics.AppC.DistributionTailSchemas

structure TailDatum where
  cutoff : ℕ
  tailMass : ℕ
  totalMass : ℕ
deriving DecidableEq, Repr

def cutoffPositive (d : TailDatum) : Prop :=
  0 < d.cutoff

def tailMassControlled (d : TailDatum) : Prop :=
  d.tailMass ≤ d.totalMass

def tailReady (d : TailDatum) : Prop :=
  cutoffPositive d ∧ tailMassControlled d

def bodyMass (d : TailDatum) : ℕ :=
  d.totalMass - d.tailMass

theorem tailReady.controlled {d : TailDatum}
    (h : tailReady d) :
    tailMassControlled d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem bodyMass_add {d : TailDatum}
    (h : tailMassControlled d) :
    bodyMass d + d.tailMass = d.totalMass := by
  unfold bodyMass tailMassControlled at *
  omega

def sampleTailDatum : TailDatum :=
  { cutoff := 5, tailMass := 3, totalMass := 10 }

example : tailReady sampleTailDatum := by
  norm_num [tailReady, cutoffPositive, tailMassControlled, sampleTailDatum]

example : bodyMass sampleTailDatum = 7 := by
  native_decide

structure TailWindow where
  cutoff : ℕ
  tailMass : ℕ
  totalMass : ℕ
  truncationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TailWindow.tailControlled (w : TailWindow) : Prop :=
  w.tailMass ≤ w.totalMass + w.slack

def TailWindow.truncationControlled (w : TailWindow) : Prop :=
  w.truncationBudget ≤ w.cutoff + w.tailMass + w.totalMass + w.slack

def tailWindowReady (w : TailWindow) : Prop :=
  0 < w.cutoff ∧
    w.tailControlled ∧
    w.truncationControlled

def TailWindow.certificate (w : TailWindow) : ℕ :=
  w.cutoff + w.tailMass + w.totalMass + w.slack

theorem tail_truncationBudget_le_certificate {w : TailWindow}
    (h : tailWindowReady w) :
    w.truncationBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htruncation⟩
  exact htruncation

def sampleTailWindow : TailWindow :=
  { cutoff := 5, tailMass := 3, totalMass := 10, truncationBudget := 17, slack := 0 }

example : tailWindowReady sampleTailWindow := by
  norm_num [tailWindowReady, TailWindow.tailControlled, TailWindow.truncationControlled,
    sampleTailWindow]

example : sampleTailWindow.certificate = 18 := by
  native_decide


structure DistributionTailSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DistributionTailSchemasBudgetCertificate.controlled
    (c : DistributionTailSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DistributionTailSchemasBudgetCertificate.budgetControlled
    (c : DistributionTailSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DistributionTailSchemasBudgetCertificate.Ready
    (c : DistributionTailSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DistributionTailSchemasBudgetCertificate.size
    (c : DistributionTailSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem distributionTailSchemas_budgetCertificate_le_size
    (c : DistributionTailSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDistributionTailSchemasBudgetCertificate :
    DistributionTailSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDistributionTailSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DistributionTailSchemasBudgetCertificate.controlled,
      sampleDistributionTailSchemasBudgetCertificate]
  · norm_num [DistributionTailSchemasBudgetCertificate.budgetControlled,
      sampleDistributionTailSchemasBudgetCertificate]

example : sampleDistributionTailSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DistributionTailSchemasBudgetCertificate.controlled,
      sampleDistributionTailSchemasBudgetCertificate]
  · norm_num [DistributionTailSchemasBudgetCertificate.budgetControlled,
      sampleDistributionTailSchemasBudgetCertificate]

example :
    sampleDistributionTailSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDistributionTailSchemasBudgetCertificate.size := by
  apply distributionTailSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DistributionTailSchemasBudgetCertificate.controlled,
      sampleDistributionTailSchemasBudgetCertificate]
  · norm_num [DistributionTailSchemasBudgetCertificate.budgetControlled,
      sampleDistributionTailSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleDistributionTailSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDistributionTailSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DistributionTailSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDistributionTailSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDistributionTailSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.DistributionTailSchemas
