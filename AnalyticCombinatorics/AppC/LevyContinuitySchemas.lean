import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Levy continuity schemas.

The finite schema records transform sample, continuity, and tail budgets.
-/

namespace AnalyticCombinatorics.AppC.LevyContinuitySchemas

structure LevyContinuityData where
  transformSamples : ℕ
  continuityBudget : ℕ
  tailBudget : ℕ
deriving DecidableEq, Repr

def samplesNonempty (d : LevyContinuityData) : Prop :=
  0 < d.transformSamples

def continuityControlled (d : LevyContinuityData) : Prop :=
  d.continuityBudget ≤ d.transformSamples + d.tailBudget

def levyContinuityReady (d : LevyContinuityData) : Prop :=
  samplesNonempty d ∧ continuityControlled d

def levyContinuityBudget (d : LevyContinuityData) : ℕ :=
  d.transformSamples + d.continuityBudget + d.tailBudget

theorem levyContinuityReady.samples {d : LevyContinuityData}
    (h : levyContinuityReady d) :
    samplesNonempty d ∧ continuityControlled d ∧ d.continuityBudget ≤ levyContinuityBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold levyContinuityBudget
  omega

theorem tailBudget_le_levyBudget (d : LevyContinuityData) :
    d.tailBudget ≤ levyContinuityBudget d := by
  unfold levyContinuityBudget
  omega

def sampleLevyContinuityData : LevyContinuityData :=
  { transformSamples := 6, continuityBudget := 9, tailBudget := 4 }

example : levyContinuityReady sampleLevyContinuityData := by
  norm_num [levyContinuityReady, samplesNonempty]
  norm_num [continuityControlled, sampleLevyContinuityData]

example : levyContinuityBudget sampleLevyContinuityData = 19 := by
  native_decide

structure LevyContinuityWindow where
  transformSamples : ℕ
  continuityBudget : ℕ
  tailBudget : ℕ
  tightnessBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LevyContinuityWindow.continuityControlled (w : LevyContinuityWindow) : Prop :=
  w.continuityBudget ≤ w.transformSamples + w.tailBudget + w.slack

def LevyContinuityWindow.tightnessControlled (w : LevyContinuityWindow) : Prop :=
  w.tightnessBudget ≤ w.transformSamples + w.continuityBudget + w.tailBudget + w.slack

def levyContinuityWindowReady (w : LevyContinuityWindow) : Prop :=
  0 < w.transformSamples ∧
    w.continuityControlled ∧
    w.tightnessControlled

def LevyContinuityWindow.certificate (w : LevyContinuityWindow) : ℕ :=
  w.transformSamples + w.continuityBudget + w.tailBudget + w.slack

theorem levyContinuity_tightnessBudget_le_certificate {w : LevyContinuityWindow}
    (h : levyContinuityWindowReady w) :
    w.tightnessBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htightness⟩
  exact htightness

def sampleLevyContinuityWindow : LevyContinuityWindow :=
  { transformSamples := 6, continuityBudget := 9, tailBudget := 4, tightnessBudget := 18,
    slack := 0 }

example : levyContinuityWindowReady sampleLevyContinuityWindow := by
  norm_num [levyContinuityWindowReady, LevyContinuityWindow.continuityControlled,
    LevyContinuityWindow.tightnessControlled, sampleLevyContinuityWindow]

example : sampleLevyContinuityWindow.certificate = 19 := by
  native_decide


structure LevyContinuitySchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LevyContinuitySchemasBudgetCertificate.controlled
    (c : LevyContinuitySchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LevyContinuitySchemasBudgetCertificate.budgetControlled
    (c : LevyContinuitySchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LevyContinuitySchemasBudgetCertificate.Ready
    (c : LevyContinuitySchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LevyContinuitySchemasBudgetCertificate.size
    (c : LevyContinuitySchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem levyContinuitySchemas_budgetCertificate_le_size
    (c : LevyContinuitySchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLevyContinuitySchemasBudgetCertificate :
    LevyContinuitySchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLevyContinuitySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LevyContinuitySchemasBudgetCertificate.controlled,
      sampleLevyContinuitySchemasBudgetCertificate]
  · norm_num [LevyContinuitySchemasBudgetCertificate.budgetControlled,
      sampleLevyContinuitySchemasBudgetCertificate]

example : sampleLevyContinuitySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LevyContinuitySchemasBudgetCertificate.controlled,
      sampleLevyContinuitySchemasBudgetCertificate]
  · norm_num [LevyContinuitySchemasBudgetCertificate.budgetControlled,
      sampleLevyContinuitySchemasBudgetCertificate]

example :
    sampleLevyContinuitySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLevyContinuitySchemasBudgetCertificate.size := by
  apply levyContinuitySchemas_budgetCertificate_le_size
  constructor
  · norm_num [LevyContinuitySchemasBudgetCertificate.controlled,
      sampleLevyContinuitySchemasBudgetCertificate]
  · norm_num [LevyContinuitySchemasBudgetCertificate.budgetControlled,
      sampleLevyContinuitySchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleLevyContinuitySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLevyContinuitySchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LevyContinuitySchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLevyContinuitySchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLevyContinuitySchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.LevyContinuitySchemas
