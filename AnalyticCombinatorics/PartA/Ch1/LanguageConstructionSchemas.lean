import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Language construction schemas.

The finite record stores alphabet size, grammar rules, and closure slack.
-/

namespace AnalyticCombinatorics.PartA.Ch1.LanguageConstructionSchemas

structure LanguageConstructionData where
  alphabetSize : ℕ
  grammarRules : ℕ
  closureSlack : ℕ
deriving DecidableEq, Repr

def alphabetSizePositive (d : LanguageConstructionData) : Prop :=
  0 < d.alphabetSize

def grammarRulesControlled (d : LanguageConstructionData) : Prop :=
  d.grammarRules ≤ d.alphabetSize + d.closureSlack

def languageConstructionReady (d : LanguageConstructionData) : Prop :=
  alphabetSizePositive d ∧ grammarRulesControlled d

def languageConstructionBudget (d : LanguageConstructionData) : ℕ :=
  d.alphabetSize + d.grammarRules + d.closureSlack

theorem languageConstructionReady.alphabet
    {d : LanguageConstructionData}
    (h : languageConstructionReady d) :
    alphabetSizePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem grammarRules_le_languageBudget (d : LanguageConstructionData) :
    d.grammarRules ≤ languageConstructionBudget d := by
  unfold languageConstructionBudget
  omega

def sampleLanguageConstructionData : LanguageConstructionData :=
  { alphabetSize := 5, grammarRules := 7, closureSlack := 3 }

example : languageConstructionReady sampleLanguageConstructionData := by
  norm_num [languageConstructionReady, alphabetSizePositive]
  norm_num [grammarRulesControlled, sampleLanguageConstructionData]

example : languageConstructionBudget sampleLanguageConstructionData = 15 := by
  native_decide

structure LanguageConstructionWindow where
  alphabetSize : ℕ
  grammarRules : ℕ
  closureSlack : ℕ
  derivationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LanguageConstructionWindow.rulesControlled (w : LanguageConstructionWindow) : Prop :=
  w.grammarRules ≤ w.alphabetSize + w.closureSlack + w.slack

def LanguageConstructionWindow.derivationControlled (w : LanguageConstructionWindow) : Prop :=
  w.derivationBudget ≤ w.alphabetSize + w.grammarRules + w.closureSlack + w.slack

def languageConstructionWindowReady (w : LanguageConstructionWindow) : Prop :=
  0 < w.alphabetSize ∧
    w.rulesControlled ∧
    w.derivationControlled

def LanguageConstructionWindow.certificate (w : LanguageConstructionWindow) : ℕ :=
  w.alphabetSize + w.grammarRules + w.closureSlack + w.slack

theorem languageConstruction_derivationBudget_le_certificate {w : LanguageConstructionWindow}
    (h : languageConstructionWindowReady w) :
    w.derivationBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hderivation⟩
  exact hderivation

def sampleLanguageConstructionWindow : LanguageConstructionWindow :=
  { alphabetSize := 5, grammarRules := 7, closureSlack := 3, derivationBudget := 14, slack := 0 }

example : languageConstructionWindowReady sampleLanguageConstructionWindow := by
  norm_num [languageConstructionWindowReady, LanguageConstructionWindow.rulesControlled,
    LanguageConstructionWindow.derivationControlled, sampleLanguageConstructionWindow]

example : sampleLanguageConstructionWindow.certificate = 15 := by
  native_decide


structure LanguageConstructionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LanguageConstructionSchemasBudgetCertificate.controlled
    (c : LanguageConstructionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LanguageConstructionSchemasBudgetCertificate.budgetControlled
    (c : LanguageConstructionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LanguageConstructionSchemasBudgetCertificate.Ready
    (c : LanguageConstructionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LanguageConstructionSchemasBudgetCertificate.size
    (c : LanguageConstructionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem languageConstructionSchemas_budgetCertificate_le_size
    (c : LanguageConstructionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLanguageConstructionSchemasBudgetCertificate :
    LanguageConstructionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLanguageConstructionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LanguageConstructionSchemasBudgetCertificate.controlled,
      sampleLanguageConstructionSchemasBudgetCertificate]
  · norm_num [LanguageConstructionSchemasBudgetCertificate.budgetControlled,
      sampleLanguageConstructionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLanguageConstructionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLanguageConstructionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLanguageConstructionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LanguageConstructionSchemasBudgetCertificate.controlled,
      sampleLanguageConstructionSchemasBudgetCertificate]
  · norm_num [LanguageConstructionSchemasBudgetCertificate.budgetControlled,
      sampleLanguageConstructionSchemasBudgetCertificate]

example :
    sampleLanguageConstructionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLanguageConstructionSchemasBudgetCertificate.size := by
  apply languageConstructionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LanguageConstructionSchemasBudgetCertificate.controlled,
      sampleLanguageConstructionSchemasBudgetCertificate]
  · norm_num [LanguageConstructionSchemasBudgetCertificate.budgetControlled,
      sampleLanguageConstructionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LanguageConstructionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLanguageConstructionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLanguageConstructionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.LanguageConstructionSchemas
