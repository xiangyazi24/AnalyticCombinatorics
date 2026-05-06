import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Monotone-density Tauberian schemas.

The file records finite monotonicity and density-window hypotheses used in
coefficient Tauberian arguments.
-/

namespace AnalyticCombinatorics.AppC.MonotoneDensitySchemas

structure DensityWindow where
  windowStart : ℕ
  windowLength : ℕ
  lowerMass : ℕ
  upperMass : ℕ
deriving DecidableEq, Repr

def nonemptyWindow (w : DensityWindow) : Prop :=
  0 < w.windowLength

def densityBracketed (w : DensityWindow) : Prop :=
  w.lowerMass ≤ w.upperMass

def monotoneDensityReady (w : DensityWindow) : Prop :=
  nonemptyWindow w ∧ densityBracketed w

def windowEnd (w : DensityWindow) : ℕ :=
  w.windowStart + w.windowLength

theorem monotoneDensityReady.bracket {w : DensityWindow}
    (h : monotoneDensityReady w) :
    densityBracketed w := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem windowEnd_ge_start (w : DensityWindow) :
    w.windowStart ≤ windowEnd w := by
  unfold windowEnd
  omega

def sampleDensityWindow : DensityWindow :=
  { windowStart := 4, windowLength := 6, lowerMass := 3, upperMass := 9 }

example : monotoneDensityReady sampleDensityWindow := by
  norm_num [monotoneDensityReady, nonemptyWindow, densityBracketed, sampleDensityWindow]

example : windowEnd sampleDensityWindow = 10 := by
  native_decide

structure MonotoneDensityCertificate where
  windowStart : ℕ
  windowLength : ℕ
  lowerMass : ℕ
  upperMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MonotoneDensityCertificate.bracketed (w : MonotoneDensityCertificate) : Prop :=
  w.lowerMass ≤ w.upperMass + w.slack

def MonotoneDensityCertificate.windowMassControlled (w : MonotoneDensityCertificate) : Prop :=
  w.upperMass ≤ w.windowStart + w.windowLength + w.lowerMass + w.slack

def monotoneDensityCertificateReady (w : MonotoneDensityCertificate) : Prop :=
  0 < w.windowLength ∧
    w.bracketed ∧
    w.windowMassControlled

def MonotoneDensityCertificate.certificate (w : MonotoneDensityCertificate) : ℕ :=
  w.windowStart + w.windowLength + w.lowerMass + w.slack

theorem monotoneDensity_upperMass_le_certificate {w : MonotoneDensityCertificate}
    (h : monotoneDensityCertificateReady w) :
    w.upperMass ≤ w.certificate := by
  rcases h with ⟨_, _, hmass⟩
  exact hmass

def sampleMonotoneDensityCertificate : MonotoneDensityCertificate :=
  { windowStart := 4, windowLength := 6, lowerMass := 3, upperMass := 9, slack := 0 }

example : monotoneDensityCertificateReady sampleMonotoneDensityCertificate := by
  norm_num [monotoneDensityCertificateReady, MonotoneDensityCertificate.bracketed,
    MonotoneDensityCertificate.windowMassControlled, sampleMonotoneDensityCertificate]

example : sampleMonotoneDensityCertificate.certificate = 13 := by
  native_decide


structure MonotoneDensitySchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MonotoneDensitySchemasBudgetCertificate.controlled
    (c : MonotoneDensitySchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MonotoneDensitySchemasBudgetCertificate.budgetControlled
    (c : MonotoneDensitySchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MonotoneDensitySchemasBudgetCertificate.Ready
    (c : MonotoneDensitySchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MonotoneDensitySchemasBudgetCertificate.size
    (c : MonotoneDensitySchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem monotoneDensitySchemas_budgetCertificate_le_size
    (c : MonotoneDensitySchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMonotoneDensitySchemasBudgetCertificate :
    MonotoneDensitySchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMonotoneDensitySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MonotoneDensitySchemasBudgetCertificate.controlled,
      sampleMonotoneDensitySchemasBudgetCertificate]
  · norm_num [MonotoneDensitySchemasBudgetCertificate.budgetControlled,
      sampleMonotoneDensitySchemasBudgetCertificate]

example : sampleMonotoneDensitySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MonotoneDensitySchemasBudgetCertificate.controlled,
      sampleMonotoneDensitySchemasBudgetCertificate]
  · norm_num [MonotoneDensitySchemasBudgetCertificate.budgetControlled,
      sampleMonotoneDensitySchemasBudgetCertificate]

example :
    sampleMonotoneDensitySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMonotoneDensitySchemasBudgetCertificate.size := by
  apply monotoneDensitySchemas_budgetCertificate_le_size
  constructor
  · norm_num [MonotoneDensitySchemasBudgetCertificate.controlled,
      sampleMonotoneDensitySchemasBudgetCertificate]
  · norm_num [MonotoneDensitySchemasBudgetCertificate.budgetControlled,
      sampleMonotoneDensitySchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleMonotoneDensitySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMonotoneDensitySchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MonotoneDensitySchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMonotoneDensitySchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMonotoneDensitySchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.MonotoneDensitySchemas
