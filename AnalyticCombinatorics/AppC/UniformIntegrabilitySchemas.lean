import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform integrability schema bookkeeping.

The finite record stores truncation level, tail mass, and common moment
budget.
-/

namespace AnalyticCombinatorics.AppC.UniformIntegrabilitySchemas

structure UniformIntegrabilityData where
  truncationLevel : ℕ
  tailMass : ℕ
  momentBudget : ℕ
deriving DecidableEq, Repr

def positiveTruncation (d : UniformIntegrabilityData) : Prop :=
  0 < d.truncationLevel

def tailMassControlled (d : UniformIntegrabilityData) : Prop :=
  d.tailMass ≤ d.momentBudget

def uniformIntegrabilityReady (d : UniformIntegrabilityData) : Prop :=
  positiveTruncation d ∧ tailMassControlled d

def integrabilityBudget (d : UniformIntegrabilityData) : ℕ :=
  d.truncationLevel + d.tailMass + d.momentBudget

theorem uniformIntegrabilityReady.tail {d : UniformIntegrabilityData}
    (h : uniformIntegrabilityReady d) :
    tailMassControlled d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem truncationLevel_le_budget (d : UniformIntegrabilityData) :
    d.truncationLevel ≤ integrabilityBudget d := by
  unfold integrabilityBudget
  omega

def sampleUniformIntegrability : UniformIntegrabilityData :=
  { truncationLevel := 6, tailMass := 3, momentBudget := 8 }

example : uniformIntegrabilityReady sampleUniformIntegrability := by
  norm_num
    [uniformIntegrabilityReady, positiveTruncation, tailMassControlled,
      sampleUniformIntegrability]

example : integrabilityBudget sampleUniformIntegrability = 17 := by
  native_decide

structure UniformIntegrabilityWindow where
  truncationWindow : ℕ
  tailWindow : ℕ
  momentWindow : ℕ
  integrabilityBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformIntegrabilityWindow.tailControlled
    (w : UniformIntegrabilityWindow) : Prop :=
  w.tailWindow ≤ w.momentWindow + w.slack

def uniformIntegrabilityWindowReady (w : UniformIntegrabilityWindow) : Prop :=
  0 < w.truncationWindow ∧ w.tailControlled ∧
    w.integrabilityBudget ≤ w.truncationWindow + w.tailWindow + w.momentWindow + w.slack

def UniformIntegrabilityWindow.certificate (w : UniformIntegrabilityWindow) : ℕ :=
  w.truncationWindow + w.tailWindow + w.momentWindow + w.integrabilityBudget + w.slack

theorem uniformIntegrability_budget_le_certificate
    (w : UniformIntegrabilityWindow) :
    w.integrabilityBudget ≤ w.certificate := by
  unfold UniformIntegrabilityWindow.certificate
  omega

def sampleUniformIntegrabilityWindow : UniformIntegrabilityWindow :=
  { truncationWindow := 5, tailWindow := 3, momentWindow := 7,
    integrabilityBudget := 16, slack := 1 }

example : uniformIntegrabilityWindowReady sampleUniformIntegrabilityWindow := by
  norm_num [uniformIntegrabilityWindowReady,
    UniformIntegrabilityWindow.tailControlled, sampleUniformIntegrabilityWindow]


structure UniformIntegrabilitySchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformIntegrabilitySchemasBudgetCertificate.controlled
    (c : UniformIntegrabilitySchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformIntegrabilitySchemasBudgetCertificate.budgetControlled
    (c : UniformIntegrabilitySchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformIntegrabilitySchemasBudgetCertificate.Ready
    (c : UniformIntegrabilitySchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformIntegrabilitySchemasBudgetCertificate.size
    (c : UniformIntegrabilitySchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformIntegrabilitySchemas_budgetCertificate_le_size
    (c : UniformIntegrabilitySchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformIntegrabilitySchemasBudgetCertificate :
    UniformIntegrabilitySchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformIntegrabilitySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformIntegrabilitySchemasBudgetCertificate.controlled,
      sampleUniformIntegrabilitySchemasBudgetCertificate]
  · norm_num [UniformIntegrabilitySchemasBudgetCertificate.budgetControlled,
      sampleUniformIntegrabilitySchemasBudgetCertificate]

example : sampleUniformIntegrabilitySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformIntegrabilitySchemasBudgetCertificate.controlled,
      sampleUniformIntegrabilitySchemasBudgetCertificate]
  · norm_num [UniformIntegrabilitySchemasBudgetCertificate.budgetControlled,
      sampleUniformIntegrabilitySchemasBudgetCertificate]

example :
    sampleUniformIntegrabilitySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformIntegrabilitySchemasBudgetCertificate.size := by
  apply uniformIntegrabilitySchemas_budgetCertificate_le_size
  constructor
  · norm_num [UniformIntegrabilitySchemasBudgetCertificate.controlled,
      sampleUniformIntegrabilitySchemasBudgetCertificate]
  · norm_num [UniformIntegrabilitySchemasBudgetCertificate.budgetControlled,
      sampleUniformIntegrabilitySchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleUniformIntegrabilitySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformIntegrabilitySchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List UniformIntegrabilitySchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformIntegrabilitySchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformIntegrabilitySchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.UniformIntegrabilitySchemas
