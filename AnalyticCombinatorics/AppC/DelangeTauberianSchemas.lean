import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Delange-style Tauberian schema bookkeeping.

The record keeps pole order, periodic fluctuation, and positivity
hypotheses as finite data.
-/

namespace AnalyticCombinatorics.AppC.DelangeTauberianSchemas

structure DelangeData where
  poleOrder : ℕ
  periodicPartControlled : Prop
  coefficientNonnegative : Prop
deriving Repr

def positivePoleOrder (d : DelangeData) : Prop :=
  0 < d.poleOrder

def delangeReady (d : DelangeData) : Prop :=
  positivePoleOrder d ∧ d.periodicPartControlled ∧ d.coefficientNonnegative

def delangeScale (d : DelangeData) : ℕ :=
  d.poleOrder + 1

theorem delangeReady.periodic {d : DelangeData}
    (h : delangeReady d) :
    d.periodicPartControlled := h.2.1

theorem delangeScale_positive (d : DelangeData) :
    0 < delangeScale d := by
  unfold delangeScale
  omega

def sampleDelange : DelangeData :=
  { poleOrder := 3, periodicPartControlled := 3 ≤ 4, coefficientNonnegative := 0 ≤ 3 }

example : delangeReady sampleDelange := by
  norm_num [delangeReady, positivePoleOrder, sampleDelange]

example : delangeScale sampleDelange = 4 := by
  native_decide

structure DelangeWindow where
  poleOrder : ℕ
  periodicAmplitude : ℕ
  coefficientMass : ℕ
  remainderSlack : ℕ
deriving DecidableEq, Repr

def DelangeWindow.poleReady (w : DelangeWindow) : Prop :=
  0 < w.poleOrder

def DelangeWindow.periodicControlled (w : DelangeWindow) : Prop :=
  w.periodicAmplitude ≤ w.coefficientMass + w.remainderSlack

def DelangeWindow.ready (w : DelangeWindow) : Prop :=
  w.poleReady ∧ w.periodicControlled

def DelangeWindow.certificate (w : DelangeWindow) : ℕ :=
  w.poleOrder + w.periodicAmplitude + w.coefficientMass + w.remainderSlack

theorem periodicAmplitude_le_certificate (w : DelangeWindow) :
    w.periodicAmplitude ≤ w.certificate := by
  unfold DelangeWindow.certificate
  omega

def sampleDelangeWindow : DelangeWindow :=
  { poleOrder := 3, periodicAmplitude := 2, coefficientMass := 5, remainderSlack := 0 }

example : sampleDelangeWindow.ready := by
  norm_num [sampleDelangeWindow, DelangeWindow.ready, DelangeWindow.poleReady,
    DelangeWindow.periodicControlled]

structure DelangeRefinementWindow where
  poleWindow : ℕ
  periodicWindow : ℕ
  coefficientWindow : ℕ
  delangeBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DelangeRefinementWindow.periodicControlled
    (w : DelangeRefinementWindow) : Prop :=
  w.periodicWindow ≤ w.coefficientWindow + w.slack

def delangeRefinementWindowReady (w : DelangeRefinementWindow) : Prop :=
  0 < w.poleWindow ∧ w.periodicControlled ∧
    w.delangeBudget ≤ w.poleWindow + w.periodicWindow + w.coefficientWindow + w.slack

def DelangeRefinementWindow.certificate (w : DelangeRefinementWindow) : ℕ :=
  w.poleWindow + w.periodicWindow + w.coefficientWindow + w.delangeBudget + w.slack

theorem delangeRefinement_budget_le_certificate
    (w : DelangeRefinementWindow) :
    w.delangeBudget ≤ w.certificate := by
  unfold DelangeRefinementWindow.certificate
  omega

def sampleDelangeRefinementWindow : DelangeRefinementWindow :=
  { poleWindow := 3, periodicWindow := 2, coefficientWindow := 5,
    delangeBudget := 11, slack := 1 }

example : delangeRefinementWindowReady sampleDelangeRefinementWindow := by
  norm_num [delangeRefinementWindowReady,
    DelangeRefinementWindow.periodicControlled, sampleDelangeRefinementWindow]


structure DelangeTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DelangeTauberianSchemasBudgetCertificate.controlled
    (c : DelangeTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DelangeTauberianSchemasBudgetCertificate.budgetControlled
    (c : DelangeTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DelangeTauberianSchemasBudgetCertificate.Ready
    (c : DelangeTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DelangeTauberianSchemasBudgetCertificate.size
    (c : DelangeTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem delangeTauberianSchemas_budgetCertificate_le_size
    (c : DelangeTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDelangeTauberianSchemasBudgetCertificate :
    DelangeTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleDelangeTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DelangeTauberianSchemasBudgetCertificate.controlled,
      sampleDelangeTauberianSchemasBudgetCertificate]
  · norm_num [DelangeTauberianSchemasBudgetCertificate.budgetControlled,
      sampleDelangeTauberianSchemasBudgetCertificate]

example :
    sampleDelangeTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDelangeTauberianSchemasBudgetCertificate.size := by
  apply delangeTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DelangeTauberianSchemasBudgetCertificate.controlled,
      sampleDelangeTauberianSchemasBudgetCertificate]
  · norm_num [DelangeTauberianSchemasBudgetCertificate.budgetControlled,
      sampleDelangeTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDelangeTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DelangeTauberianSchemasBudgetCertificate.controlled,
      sampleDelangeTauberianSchemasBudgetCertificate]
  · norm_num [DelangeTauberianSchemasBudgetCertificate.budgetControlled,
      sampleDelangeTauberianSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDelangeTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDelangeTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DelangeTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDelangeTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDelangeTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.DelangeTauberianSchemas
