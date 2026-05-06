import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite ordinary construction models.

The finite schema records atom budget, construction steps, and closure
slack for ordinary symbolic constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteOrdinaryConstructionModels

structure OrdinaryConstructionData where
  atomBudget : ℕ
  constructionSteps : ℕ
  closureSlack : ℕ
deriving DecidableEq, Repr

def atomBudgetPositive (d : OrdinaryConstructionData) : Prop :=
  0 < d.atomBudget

def constructionStepsControlled (d : OrdinaryConstructionData) : Prop :=
  d.constructionSteps ≤ d.atomBudget + d.closureSlack

def ordinaryConstructionReady (d : OrdinaryConstructionData) : Prop :=
  atomBudgetPositive d ∧ constructionStepsControlled d

def ordinaryConstructionBudget (d : OrdinaryConstructionData) : ℕ :=
  d.atomBudget + d.constructionSteps + d.closureSlack

theorem ordinaryConstructionReady.atoms {d : OrdinaryConstructionData}
    (h : ordinaryConstructionReady d) :
    atomBudgetPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem constructionSteps_le_ordinaryBudget
    (d : OrdinaryConstructionData) :
    d.constructionSteps ≤ ordinaryConstructionBudget d := by
  unfold ordinaryConstructionBudget
  omega

def sampleOrdinaryConstructionData : OrdinaryConstructionData :=
  { atomBudget := 6, constructionSteps := 8, closureSlack := 3 }

example : ordinaryConstructionReady sampleOrdinaryConstructionData := by
  norm_num [ordinaryConstructionReady, atomBudgetPositive]
  norm_num [constructionStepsControlled, sampleOrdinaryConstructionData]

example : ordinaryConstructionBudget sampleOrdinaryConstructionData = 17 := by
  native_decide

structure OrdinaryConstructionWindow where
  atomBudget : ℕ
  constructionSteps : ℕ
  closureSlack : ℕ
  grammarBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def OrdinaryConstructionWindow.stepsControlled (w : OrdinaryConstructionWindow) : Prop :=
  w.constructionSteps ≤ w.atomBudget + w.closureSlack + w.slack

def OrdinaryConstructionWindow.grammarControlled (w : OrdinaryConstructionWindow) : Prop :=
  w.grammarBudget ≤ w.atomBudget + w.constructionSteps + w.closureSlack + w.slack

def ordinaryConstructionWindowReady (w : OrdinaryConstructionWindow) : Prop :=
  0 < w.atomBudget ∧
    w.stepsControlled ∧
    w.grammarControlled

def OrdinaryConstructionWindow.certificate (w : OrdinaryConstructionWindow) : ℕ :=
  w.atomBudget + w.constructionSteps + w.closureSlack + w.slack

theorem ordinaryConstruction_grammarBudget_le_certificate {w : OrdinaryConstructionWindow}
    (h : ordinaryConstructionWindowReady w) :
    w.grammarBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hgrammar⟩
  exact hgrammar

def sampleOrdinaryConstructionWindow : OrdinaryConstructionWindow :=
  { atomBudget := 6, constructionSteps := 8, closureSlack := 3, grammarBudget := 16, slack := 0 }

example : ordinaryConstructionWindowReady sampleOrdinaryConstructionWindow := by
  norm_num [ordinaryConstructionWindowReady, OrdinaryConstructionWindow.stepsControlled,
    OrdinaryConstructionWindow.grammarControlled, sampleOrdinaryConstructionWindow]

example : sampleOrdinaryConstructionWindow.certificate = 17 := by
  native_decide


structure FiniteOrdinaryConstructionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteOrdinaryConstructionModelsBudgetCertificate.controlled
    (c : FiniteOrdinaryConstructionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteOrdinaryConstructionModelsBudgetCertificate.budgetControlled
    (c : FiniteOrdinaryConstructionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteOrdinaryConstructionModelsBudgetCertificate.Ready
    (c : FiniteOrdinaryConstructionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteOrdinaryConstructionModelsBudgetCertificate.size
    (c : FiniteOrdinaryConstructionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteOrdinaryConstructionModels_budgetCertificate_le_size
    (c : FiniteOrdinaryConstructionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteOrdinaryConstructionModelsBudgetCertificate :
    FiniteOrdinaryConstructionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteOrdinaryConstructionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteOrdinaryConstructionModelsBudgetCertificate.controlled,
      sampleFiniteOrdinaryConstructionModelsBudgetCertificate]
  · norm_num [FiniteOrdinaryConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteOrdinaryConstructionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteOrdinaryConstructionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteOrdinaryConstructionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteOrdinaryConstructionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteOrdinaryConstructionModelsBudgetCertificate.controlled,
      sampleFiniteOrdinaryConstructionModelsBudgetCertificate]
  · norm_num [FiniteOrdinaryConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteOrdinaryConstructionModelsBudgetCertificate]

example :
    sampleFiniteOrdinaryConstructionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteOrdinaryConstructionModelsBudgetCertificate.size := by
  apply finiteOrdinaryConstructionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteOrdinaryConstructionModelsBudgetCertificate.controlled,
      sampleFiniteOrdinaryConstructionModelsBudgetCertificate]
  · norm_num [FiniteOrdinaryConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteOrdinaryConstructionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteOrdinaryConstructionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteOrdinaryConstructionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteOrdinaryConstructionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteOrdinaryConstructionModels
