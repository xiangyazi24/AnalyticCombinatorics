import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Power-law tail schemas for universal limit estimates.

The file records the integer hypotheses used to state that a tail has enough
decay beyond a cutoff.
-/

namespace AnalyticCombinatorics.AppC.PowerLawTailSchemas

structure PowerTailData where
  exponent : ℕ
  cutoff : ℕ
  massBudget : ℕ
deriving DecidableEq, Repr

def summableExponent (d : PowerTailData) : Prop :=
  1 < d.exponent

def tailBudgetReady (d : PowerTailData) : Prop :=
  summableExponent d ∧ d.cutoff ≤ d.massBudget

def tailScale (d : PowerTailData) : ℕ :=
  d.cutoff ^ d.exponent

theorem tailBudgetReady.exponent {d : PowerTailData}
    (h : tailBudgetReady d) :
    summableExponent d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem summableExponent_positive {d : PowerTailData}
    (h : summableExponent d) :
    0 < d.exponent := by
  unfold summableExponent at h
  omega

def sampleTail : PowerTailData :=
  { exponent := 3, cutoff := 5, massBudget := 8 }

example : tailBudgetReady sampleTail := by
  norm_num [tailBudgetReady, summableExponent, sampleTail]

example : tailScale sampleTail = 125 := by
  native_decide

structure PowerLawTailWindow where
  exponent : ℕ
  cutoff : ℕ
  tailMass : ℕ
  envelopeBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PowerLawTailWindow.exponentReady (w : PowerLawTailWindow) : Prop :=
  1 < w.exponent

def PowerLawTailWindow.tailControlled (w : PowerLawTailWindow) : Prop :=
  w.tailMass ≤ w.envelopeBudget + w.slack

def PowerLawTailWindow.cutoffControlled (w : PowerLawTailWindow) : Prop :=
  w.cutoff ≤ w.envelopeBudget + w.slack

def PowerLawTailWindow.ready (w : PowerLawTailWindow) : Prop :=
  w.exponentReady ∧ w.tailControlled ∧ w.cutoffControlled

def PowerLawTailWindow.certificate (w : PowerLawTailWindow) : ℕ :=
  w.exponent + w.cutoff + w.tailMass + w.envelopeBudget + w.slack

theorem tailMass_le_certificate (w : PowerLawTailWindow) :
    w.tailMass ≤ w.certificate := by
  unfold PowerLawTailWindow.certificate
  omega

def samplePowerLawTailWindow : PowerLawTailWindow :=
  { exponent := 3, cutoff := 5, tailMass := 4, envelopeBudget := 8, slack := 0 }

example : samplePowerLawTailWindow.ready := by
  norm_num [samplePowerLawTailWindow, PowerLawTailWindow.ready,
    PowerLawTailWindow.exponentReady, PowerLawTailWindow.tailControlled,
    PowerLawTailWindow.cutoffControlled]

structure PowerLawTailRefinementWindow where
  exponentWindow : ℕ
  cutoffWindow : ℕ
  tailWindow : ℕ
  envelopeWindow : ℕ
  tailBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PowerLawTailRefinementWindow.tailControlled
    (w : PowerLawTailRefinementWindow) : Prop :=
  w.tailWindow ≤ w.envelopeWindow + w.slack

def powerLawTailRefinementWindowReady
    (w : PowerLawTailRefinementWindow) : Prop :=
  1 < w.exponentWindow ∧ w.tailControlled ∧
    w.tailBudget ≤ w.exponentWindow + w.cutoffWindow + w.tailWindow + w.slack

def PowerLawTailRefinementWindow.certificate
    (w : PowerLawTailRefinementWindow) : ℕ :=
  w.exponentWindow + w.cutoffWindow + w.tailWindow + w.envelopeWindow +
    w.tailBudget + w.slack

theorem powerLawTailRefinement_budget_le_certificate
    (w : PowerLawTailRefinementWindow) :
    w.tailBudget ≤ w.certificate := by
  unfold PowerLawTailRefinementWindow.certificate
  omega

def samplePowerLawTailRefinementWindow : PowerLawTailRefinementWindow :=
  { exponentWindow := 3, cutoffWindow := 5, tailWindow := 4,
    envelopeWindow := 8, tailBudget := 13, slack := 1 }

example : powerLawTailRefinementWindowReady
    samplePowerLawTailRefinementWindow := by
  norm_num [powerLawTailRefinementWindowReady,
    PowerLawTailRefinementWindow.tailControlled, samplePowerLawTailRefinementWindow]


structure PowerLawTailSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PowerLawTailSchemasBudgetCertificate.controlled
    (c : PowerLawTailSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PowerLawTailSchemasBudgetCertificate.budgetControlled
    (c : PowerLawTailSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PowerLawTailSchemasBudgetCertificate.Ready
    (c : PowerLawTailSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PowerLawTailSchemasBudgetCertificate.size
    (c : PowerLawTailSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem powerLawTailSchemas_budgetCertificate_le_size
    (c : PowerLawTailSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePowerLawTailSchemasBudgetCertificate :
    PowerLawTailSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePowerLawTailSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PowerLawTailSchemasBudgetCertificate.controlled,
      samplePowerLawTailSchemasBudgetCertificate]
  · norm_num [PowerLawTailSchemasBudgetCertificate.budgetControlled,
      samplePowerLawTailSchemasBudgetCertificate]

example :
    samplePowerLawTailSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePowerLawTailSchemasBudgetCertificate.size := by
  apply powerLawTailSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PowerLawTailSchemasBudgetCertificate.controlled,
      samplePowerLawTailSchemasBudgetCertificate]
  · norm_num [PowerLawTailSchemasBudgetCertificate.budgetControlled,
      samplePowerLawTailSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePowerLawTailSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PowerLawTailSchemasBudgetCertificate.controlled,
      samplePowerLawTailSchemasBudgetCertificate]
  · norm_num [PowerLawTailSchemasBudgetCertificate.budgetControlled,
      samplePowerLawTailSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePowerLawTailSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePowerLawTailSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PowerLawTailSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePowerLawTailSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePowerLawTailSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.PowerLawTailSchemas
