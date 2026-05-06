import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Skorokhod tightness schemas.

The finite schema records mesh count, oscillation budget, and compact
containment slack.
-/

namespace AnalyticCombinatorics.AppC.SkorokhodTightnessSchemas

structure SkorokhodTightnessData where
  meshCount : ℕ
  oscillationBudget : ℕ
  containmentSlack : ℕ
deriving DecidableEq, Repr

def meshNonempty (d : SkorokhodTightnessData) : Prop :=
  0 < d.meshCount

def oscillationControlled (d : SkorokhodTightnessData) : Prop :=
  d.oscillationBudget ≤ d.meshCount + d.containmentSlack

def skorokhodTightnessReady (d : SkorokhodTightnessData) : Prop :=
  meshNonempty d ∧ oscillationControlled d

def skorokhodTightnessBudget (d : SkorokhodTightnessData) : ℕ :=
  d.meshCount + d.oscillationBudget + d.containmentSlack

theorem skorokhodTightnessReady.mesh {d : SkorokhodTightnessData}
    (h : skorokhodTightnessReady d) :
    meshNonempty d ∧ oscillationControlled d ∧
      d.oscillationBudget ≤ skorokhodTightnessBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold skorokhodTightnessBudget
  omega

theorem oscillationBudget_le_skorokhodBudget
    (d : SkorokhodTightnessData) :
    d.oscillationBudget ≤ skorokhodTightnessBudget d := by
  unfold skorokhodTightnessBudget
  omega

def sampleSkorokhodTightnessData : SkorokhodTightnessData :=
  { meshCount := 6, oscillationBudget := 8, containmentSlack := 3 }

example : skorokhodTightnessReady sampleSkorokhodTightnessData := by
  norm_num [skorokhodTightnessReady, meshNonempty]
  norm_num [oscillationControlled, sampleSkorokhodTightnessData]

example : skorokhodTightnessBudget sampleSkorokhodTightnessData = 17 := by
  native_decide

structure SkorokhodTightnessWindow where
  meshWindow : ℕ
  oscillationWindow : ℕ
  containmentSlack : ℕ
  tightnessBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SkorokhodTightnessWindow.oscillationControlled
    (w : SkorokhodTightnessWindow) : Prop :=
  w.oscillationWindow ≤ w.meshWindow + w.containmentSlack + w.slack

def skorokhodTightnessWindowReady (w : SkorokhodTightnessWindow) : Prop :=
  0 < w.meshWindow ∧ w.oscillationControlled ∧
    w.tightnessBudget ≤ w.meshWindow + w.oscillationWindow + w.slack

def SkorokhodTightnessWindow.certificate (w : SkorokhodTightnessWindow) : ℕ :=
  w.meshWindow + w.oscillationWindow + w.containmentSlack + w.tightnessBudget + w.slack

theorem skorokhodTightness_tightnessBudget_le_certificate
    (w : SkorokhodTightnessWindow) :
    w.tightnessBudget ≤ w.certificate := by
  unfold SkorokhodTightnessWindow.certificate
  omega

def sampleSkorokhodTightnessWindow : SkorokhodTightnessWindow :=
  { meshWindow := 5, oscillationWindow := 7, containmentSlack := 2,
    tightnessBudget := 14, slack := 2 }

example : skorokhodTightnessWindowReady sampleSkorokhodTightnessWindow := by
  norm_num [skorokhodTightnessWindowReady,
    SkorokhodTightnessWindow.oscillationControlled, sampleSkorokhodTightnessWindow]


structure SkorokhodTightnessSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SkorokhodTightnessSchemasBudgetCertificate.controlled
    (c : SkorokhodTightnessSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SkorokhodTightnessSchemasBudgetCertificate.budgetControlled
    (c : SkorokhodTightnessSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SkorokhodTightnessSchemasBudgetCertificate.Ready
    (c : SkorokhodTightnessSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SkorokhodTightnessSchemasBudgetCertificate.size
    (c : SkorokhodTightnessSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem skorokhodTightnessSchemas_budgetCertificate_le_size
    (c : SkorokhodTightnessSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSkorokhodTightnessSchemasBudgetCertificate :
    SkorokhodTightnessSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSkorokhodTightnessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SkorokhodTightnessSchemasBudgetCertificate.controlled,
      sampleSkorokhodTightnessSchemasBudgetCertificate]
  · norm_num [SkorokhodTightnessSchemasBudgetCertificate.budgetControlled,
      sampleSkorokhodTightnessSchemasBudgetCertificate]

example : sampleSkorokhodTightnessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SkorokhodTightnessSchemasBudgetCertificate.controlled,
      sampleSkorokhodTightnessSchemasBudgetCertificate]
  · norm_num [SkorokhodTightnessSchemasBudgetCertificate.budgetControlled,
      sampleSkorokhodTightnessSchemasBudgetCertificate]

example :
    sampleSkorokhodTightnessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSkorokhodTightnessSchemasBudgetCertificate.size := by
  apply skorokhodTightnessSchemas_budgetCertificate_le_size
  constructor
  · norm_num [SkorokhodTightnessSchemasBudgetCertificate.controlled,
      sampleSkorokhodTightnessSchemasBudgetCertificate]
  · norm_num [SkorokhodTightnessSchemasBudgetCertificate.budgetControlled,
      sampleSkorokhodTightnessSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleSkorokhodTightnessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSkorokhodTightnessSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SkorokhodTightnessSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSkorokhodTightnessSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSkorokhodTightnessSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.SkorokhodTightnessSchemas
