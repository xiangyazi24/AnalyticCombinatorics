import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cesaro Tauberian schema bookkeeping.

The file records finite average numerators and denominator positivity for
Cesaro-type convergence hypotheses.
-/

namespace AnalyticCombinatorics.AppC.CesaroTauberianSchemas

structure CesaroDatum where
  averageNumerator : ℕ
  averageDenominator : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def positiveAverageDenominator (d : CesaroDatum) : Prop :=
  0 < d.averageDenominator

def cesaroErrorControlled (d : CesaroDatum) : Prop :=
  d.errorBudget ≤ d.averageNumerator + d.averageDenominator

def cesaroReady (d : CesaroDatum) : Prop :=
  positiveAverageDenominator d ∧ cesaroErrorControlled d

def cesaroScale (d : CesaroDatum) : ℕ :=
  d.averageNumerator + d.averageDenominator + d.errorBudget

theorem cesaroReady.denominator {d : CesaroDatum}
    (h : cesaroReady d) :
    positiveAverageDenominator d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem averageDenominator_le_scale (d : CesaroDatum) :
    d.averageDenominator ≤ cesaroScale d := by
  unfold cesaroScale
  omega

def sampleCesaro : CesaroDatum :=
  { averageNumerator := 7, averageDenominator := 4, errorBudget := 3 }

example : cesaroReady sampleCesaro := by
  norm_num [cesaroReady, positiveAverageDenominator, cesaroErrorControlled, sampleCesaro]

example : cesaroScale sampleCesaro = 14 := by
  native_decide

structure CesaroWindow where
  averageNumerator : ℕ
  averageDenominator : ℕ
  errorBudget : ℕ
  summatoryBudget : ℕ
deriving DecidableEq, Repr

def CesaroWindow.denominatorReady (w : CesaroWindow) : Prop :=
  0 < w.averageDenominator

def CesaroWindow.errorControlled (w : CesaroWindow) : Prop :=
  w.errorBudget ≤ w.averageNumerator + w.averageDenominator

def CesaroWindow.summatoryControlled (w : CesaroWindow) : Prop :=
  w.summatoryBudget ≤ w.averageNumerator + w.averageDenominator + w.errorBudget

def CesaroWindow.ready (w : CesaroWindow) : Prop :=
  w.denominatorReady ∧ w.errorControlled ∧ w.summatoryControlled

def CesaroWindow.certificate (w : CesaroWindow) : ℕ :=
  w.averageNumerator + w.averageDenominator + w.errorBudget + w.summatoryBudget

theorem summatoryBudget_le_certificate (w : CesaroWindow) :
    w.summatoryBudget ≤ w.certificate := by
  unfold CesaroWindow.certificate
  omega

def sampleCesaroWindow : CesaroWindow :=
  { averageNumerator := 7, averageDenominator := 4, errorBudget := 3, summatoryBudget := 10 }

example : sampleCesaroWindow.ready := by
  norm_num [sampleCesaroWindow, CesaroWindow.ready, CesaroWindow.denominatorReady,
    CesaroWindow.errorControlled, CesaroWindow.summatoryControlled]

structure CesaroRefinementWindow where
  numeratorWindow : ℕ
  denominatorWindow : ℕ
  errorWindow : ℕ
  summatoryWindow : ℕ
  cesaroBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CesaroRefinementWindow.summatoryControlled
    (w : CesaroRefinementWindow) : Prop :=
  w.summatoryWindow ≤ w.numeratorWindow + w.denominatorWindow + w.errorWindow + w.slack

def cesaroRefinementWindowReady (w : CesaroRefinementWindow) : Prop :=
  0 < w.denominatorWindow ∧ w.summatoryControlled ∧
    w.cesaroBudget ≤ w.numeratorWindow + w.denominatorWindow + w.summatoryWindow + w.slack

def CesaroRefinementWindow.certificate (w : CesaroRefinementWindow) : ℕ :=
  w.numeratorWindow + w.denominatorWindow + w.errorWindow + w.summatoryWindow +
    w.cesaroBudget + w.slack

theorem cesaroRefinement_budget_le_certificate
    (w : CesaroRefinementWindow) :
    w.cesaroBudget ≤ w.certificate := by
  unfold CesaroRefinementWindow.certificate
  omega

def sampleCesaroRefinementWindow : CesaroRefinementWindow :=
  { numeratorWindow := 7, denominatorWindow := 4, errorWindow := 3,
    summatoryWindow := 10, cesaroBudget := 22, slack := 1 }

example : cesaroRefinementWindowReady sampleCesaroRefinementWindow := by
  norm_num [cesaroRefinementWindowReady,
    CesaroRefinementWindow.summatoryControlled, sampleCesaroRefinementWindow]


structure CesaroTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CesaroTauberianSchemasBudgetCertificate.controlled
    (c : CesaroTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CesaroTauberianSchemasBudgetCertificate.budgetControlled
    (c : CesaroTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CesaroTauberianSchemasBudgetCertificate.Ready
    (c : CesaroTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CesaroTauberianSchemasBudgetCertificate.size
    (c : CesaroTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cesaroTauberianSchemas_budgetCertificate_le_size
    (c : CesaroTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCesaroTauberianSchemasBudgetCertificate :
    CesaroTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCesaroTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CesaroTauberianSchemasBudgetCertificate.controlled,
      sampleCesaroTauberianSchemasBudgetCertificate]
  · norm_num [CesaroTauberianSchemasBudgetCertificate.budgetControlled,
      sampleCesaroTauberianSchemasBudgetCertificate]

example :
    sampleCesaroTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCesaroTauberianSchemasBudgetCertificate.size := by
  apply cesaroTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CesaroTauberianSchemasBudgetCertificate.controlled,
      sampleCesaroTauberianSchemasBudgetCertificate]
  · norm_num [CesaroTauberianSchemasBudgetCertificate.budgetControlled,
      sampleCesaroTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCesaroTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CesaroTauberianSchemasBudgetCertificate.controlled,
      sampleCesaroTauberianSchemasBudgetCertificate]
  · norm_num [CesaroTauberianSchemasBudgetCertificate.budgetControlled,
      sampleCesaroTauberianSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCesaroTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCesaroTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CesaroTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCesaroTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCesaroTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.CesaroTauberianSchemas
