import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Entropy tightness schemas.

The finite schema records entropy budget, covering number, and tail slack.
-/

namespace AnalyticCombinatorics.AppC.EntropyTightnessSchemas

structure EntropyTightnessData where
  entropyBudget : ℕ
  coveringNumber : ℕ
  tailSlack : ℕ
deriving DecidableEq, Repr

def coveringNumberPositive (d : EntropyTightnessData) : Prop :=
  0 < d.coveringNumber

def entropyControlled (d : EntropyTightnessData) : Prop :=
  d.entropyBudget ≤ d.coveringNumber + d.tailSlack

def entropyTightnessReady (d : EntropyTightnessData) : Prop :=
  coveringNumberPositive d ∧ entropyControlled d

def entropyTightnessBudget (d : EntropyTightnessData) : ℕ :=
  d.entropyBudget + d.coveringNumber + d.tailSlack

theorem entropyTightnessReady.covering {d : EntropyTightnessData}
    (h : entropyTightnessReady d) :
    coveringNumberPositive d ∧ entropyControlled d ∧
      d.entropyBudget ≤ entropyTightnessBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold entropyTightnessBudget
  omega

theorem entropyBudget_le_entropyTightnessBudget
    (d : EntropyTightnessData) :
    d.entropyBudget ≤ entropyTightnessBudget d := by
  unfold entropyTightnessBudget
  omega

def sampleEntropyTightnessData : EntropyTightnessData :=
  { entropyBudget := 7, coveringNumber := 5, tailSlack := 3 }

example : entropyTightnessReady sampleEntropyTightnessData := by
  norm_num [entropyTightnessReady, coveringNumberPositive]
  norm_num [entropyControlled, sampleEntropyTightnessData]

example : entropyTightnessBudget sampleEntropyTightnessData = 15 := by
  native_decide

structure EntropyTightnessWindow where
  entropyWindow : ℕ
  coveringWindow : ℕ
  tailSlack : ℕ
  tightnessBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EntropyTightnessWindow.entropyControlled (w : EntropyTightnessWindow) : Prop :=
  w.entropyWindow ≤ w.coveringWindow + w.tailSlack + w.slack

def entropyTightnessWindowReady (w : EntropyTightnessWindow) : Prop :=
  0 < w.coveringWindow ∧ w.entropyControlled ∧
    w.tightnessBudget ≤ w.entropyWindow + w.coveringWindow + w.slack

def EntropyTightnessWindow.certificate (w : EntropyTightnessWindow) : ℕ :=
  w.entropyWindow + w.coveringWindow + w.tailSlack + w.tightnessBudget + w.slack

theorem entropyTightness_tightnessBudget_le_certificate
    (w : EntropyTightnessWindow) :
    w.tightnessBudget ≤ w.certificate := by
  unfold EntropyTightnessWindow.certificate
  omega

def sampleEntropyTightnessWindow : EntropyTightnessWindow :=
  { entropyWindow := 6, coveringWindow := 5, tailSlack := 2, tightnessBudget := 12, slack := 1 }

example : entropyTightnessWindowReady sampleEntropyTightnessWindow := by
  norm_num [entropyTightnessWindowReady, EntropyTightnessWindow.entropyControlled,
    sampleEntropyTightnessWindow]


structure EntropyTightnessSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EntropyTightnessSchemasBudgetCertificate.controlled
    (c : EntropyTightnessSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def EntropyTightnessSchemasBudgetCertificate.budgetControlled
    (c : EntropyTightnessSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def EntropyTightnessSchemasBudgetCertificate.Ready
    (c : EntropyTightnessSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EntropyTightnessSchemasBudgetCertificate.size
    (c : EntropyTightnessSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem entropyTightnessSchemas_budgetCertificate_le_size
    (c : EntropyTightnessSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEntropyTightnessSchemasBudgetCertificate :
    EntropyTightnessSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleEntropyTightnessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EntropyTightnessSchemasBudgetCertificate.controlled,
      sampleEntropyTightnessSchemasBudgetCertificate]
  · norm_num [EntropyTightnessSchemasBudgetCertificate.budgetControlled,
      sampleEntropyTightnessSchemasBudgetCertificate]

example : sampleEntropyTightnessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EntropyTightnessSchemasBudgetCertificate.controlled,
      sampleEntropyTightnessSchemasBudgetCertificate]
  · norm_num [EntropyTightnessSchemasBudgetCertificate.budgetControlled,
      sampleEntropyTightnessSchemasBudgetCertificate]

example :
    sampleEntropyTightnessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEntropyTightnessSchemasBudgetCertificate.size := by
  apply entropyTightnessSchemas_budgetCertificate_le_size
  constructor
  · norm_num [EntropyTightnessSchemasBudgetCertificate.controlled,
      sampleEntropyTightnessSchemasBudgetCertificate]
  · norm_num [EntropyTightnessSchemasBudgetCertificate.budgetControlled,
      sampleEntropyTightnessSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleEntropyTightnessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEntropyTightnessSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List EntropyTightnessSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEntropyTightnessSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleEntropyTightnessSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.EntropyTightnessSchemas
