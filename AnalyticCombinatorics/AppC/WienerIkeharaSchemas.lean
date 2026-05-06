import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Wiener-Ikehara style Tauberian schema bookkeeping.

The analytic continuation and pole hypotheses are represented as a finite
record of flags and residue budgets.
-/

namespace AnalyticCombinatorics.AppC.WienerIkeharaSchemas

structure WienerIkeharaData where
  simplePole : Prop
  positiveResidue : Prop
  boundaryContinuation : Prop
  residueBudget : ℕ
deriving Repr

def wienerIkeharaReady (d : WienerIkeharaData) : Prop :=
  d.simplePole ∧ d.positiveResidue ∧ d.boundaryContinuation

def residueScale (d : WienerIkeharaData) : ℕ :=
  d.residueBudget + 1

theorem wienerIkeharaReady.residue {d : WienerIkeharaData}
    (h : wienerIkeharaReady d) :
    d.positiveResidue := h.2.1

theorem residueScale_positive (d : WienerIkeharaData) :
    0 < residueScale d := by
  unfold residueScale
  omega

def sampleWienerIkehara : WienerIkeharaData :=
  { simplePole := 1 ≤ 7, positiveResidue := 0 < 7, boundaryContinuation := 7 ≤ 7,
    residueBudget := 7 }

example : wienerIkeharaReady sampleWienerIkehara := by
  norm_num [wienerIkeharaReady, sampleWienerIkehara]

example : residueScale sampleWienerIkehara = 8 := by
  native_decide

structure WienerIkeharaWindow where
  poleOrder : ℕ
  residueNumerator : ℕ
  residueDenominator : ℕ
  boundaryWidth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WienerIkeharaWindow.simplePoleReady (w : WienerIkeharaWindow) : Prop :=
  w.poleOrder = 1

def WienerIkeharaWindow.residueReady (w : WienerIkeharaWindow) : Prop :=
  0 < w.residueNumerator ∧ 0 < w.residueDenominator

def WienerIkeharaWindow.boundaryControlled (w : WienerIkeharaWindow) : Prop :=
  w.boundaryWidth ≤ w.residueNumerator + w.slack

def WienerIkeharaWindow.ready (w : WienerIkeharaWindow) : Prop :=
  w.simplePoleReady ∧ w.residueReady ∧ w.boundaryControlled

def WienerIkeharaWindow.certificate (w : WienerIkeharaWindow) : ℕ :=
  w.poleOrder + w.residueNumerator + w.residueDenominator + w.boundaryWidth + w.slack

theorem boundaryWidth_le_certificate (w : WienerIkeharaWindow) :
    w.boundaryWidth ≤ w.certificate := by
  unfold WienerIkeharaWindow.certificate
  omega

def sampleWienerIkeharaWindow : WienerIkeharaWindow :=
  { poleOrder := 1, residueNumerator := 7, residueDenominator := 2,
    boundaryWidth := 5, slack := 0 }

example : sampleWienerIkeharaWindow.ready := by
  norm_num [sampleWienerIkeharaWindow, WienerIkeharaWindow.ready,
    WienerIkeharaWindow.simplePoleReady, WienerIkeharaWindow.residueReady,
    WienerIkeharaWindow.boundaryControlled]

structure WienerIkeharaRefinementWindow where
  poleWindow : ℕ
  residueWindow : ℕ
  boundaryWindow : ℕ
  ikeharaBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WienerIkeharaRefinementWindow.boundaryControlled
    (w : WienerIkeharaRefinementWindow) : Prop :=
  w.boundaryWindow ≤ w.residueWindow + w.slack

def wienerIkeharaRefinementWindowReady
    (w : WienerIkeharaRefinementWindow) : Prop :=
  w.poleWindow = 1 ∧ 0 < w.residueWindow ∧ w.boundaryControlled ∧
    w.ikeharaBudget ≤ w.poleWindow + w.residueWindow + w.boundaryWindow + w.slack

def WienerIkeharaRefinementWindow.certificate
    (w : WienerIkeharaRefinementWindow) : ℕ :=
  w.poleWindow + w.residueWindow + w.boundaryWindow + w.ikeharaBudget + w.slack

theorem wienerIkeharaRefinement_budget_le_certificate
    (w : WienerIkeharaRefinementWindow) :
    w.ikeharaBudget ≤ w.certificate := by
  unfold WienerIkeharaRefinementWindow.certificate
  omega

def sampleWienerIkeharaRefinementWindow :
    WienerIkeharaRefinementWindow :=
  { poleWindow := 1, residueWindow := 7, boundaryWindow := 5,
    ikeharaBudget := 14, slack := 1 }

example : wienerIkeharaRefinementWindowReady
    sampleWienerIkeharaRefinementWindow := by
  norm_num [wienerIkeharaRefinementWindowReady,
    WienerIkeharaRefinementWindow.boundaryControlled,
    sampleWienerIkeharaRefinementWindow]


structure WienerIkeharaSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WienerIkeharaSchemasBudgetCertificate.controlled
    (c : WienerIkeharaSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def WienerIkeharaSchemasBudgetCertificate.budgetControlled
    (c : WienerIkeharaSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def WienerIkeharaSchemasBudgetCertificate.Ready
    (c : WienerIkeharaSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WienerIkeharaSchemasBudgetCertificate.size
    (c : WienerIkeharaSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem wienerIkeharaSchemas_budgetCertificate_le_size
    (c : WienerIkeharaSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWienerIkeharaSchemasBudgetCertificate :
    WienerIkeharaSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleWienerIkeharaSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [WienerIkeharaSchemasBudgetCertificate.controlled,
      sampleWienerIkeharaSchemasBudgetCertificate]
  · norm_num [WienerIkeharaSchemasBudgetCertificate.budgetControlled,
      sampleWienerIkeharaSchemasBudgetCertificate]

example :
    sampleWienerIkeharaSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleWienerIkeharaSchemasBudgetCertificate.size := by
  apply wienerIkeharaSchemas_budgetCertificate_le_size
  constructor
  · norm_num [WienerIkeharaSchemasBudgetCertificate.controlled,
      sampleWienerIkeharaSchemasBudgetCertificate]
  · norm_num [WienerIkeharaSchemasBudgetCertificate.budgetControlled,
      sampleWienerIkeharaSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleWienerIkeharaSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [WienerIkeharaSchemasBudgetCertificate.controlled,
      sampleWienerIkeharaSchemasBudgetCertificate]
  · norm_num [WienerIkeharaSchemasBudgetCertificate.budgetControlled,
      sampleWienerIkeharaSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWienerIkeharaSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleWienerIkeharaSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List WienerIkeharaSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleWienerIkeharaSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleWienerIkeharaSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.WienerIkeharaSchemas
