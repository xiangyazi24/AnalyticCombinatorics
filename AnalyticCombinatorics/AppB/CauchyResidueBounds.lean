import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cauchy residue bound bookkeeping.

Residue extraction is represented by finite pole order, contour size, and
residue-budget inequalities.
-/

namespace AnalyticCombinatorics.AppB.CauchyResidueBounds

structure ResidueBoundDatum where
  poleOrder : ℕ
  contourBudget : ℕ
  residueBudget : ℕ
deriving DecidableEq, Repr

def positivePoleOrder (d : ResidueBoundDatum) : Prop :=
  0 < d.poleOrder

def residueBounded (d : ResidueBoundDatum) : Prop :=
  d.residueBudget ≤ d.poleOrder * d.contourBudget

def residueEstimateReady (d : ResidueBoundDatum) : Prop :=
  positivePoleOrder d ∧ residueBounded d

def residueSlack (d : ResidueBoundDatum) : ℕ :=
  d.poleOrder * d.contourBudget - d.residueBudget

theorem residueEstimateReady.bound {d : ResidueBoundDatum}
    (h : residueEstimateReady d) :
    positivePoleOrder d ∧ residueBounded d := by
  refine ⟨h.1, h.2⟩

theorem residueSlack_add {d : ResidueBoundDatum}
    (h : residueBounded d) :
    residueSlack d + d.residueBudget = d.poleOrder * d.contourBudget := by
  unfold residueSlack residueBounded at *
  omega

def sampleResidueBound : ResidueBoundDatum :=
  { poleOrder := 2, contourBudget := 7, residueBudget := 5 }

example : residueEstimateReady sampleResidueBound := by
  norm_num [residueEstimateReady, positivePoleOrder, residueBounded, sampleResidueBound]

example : residueSlack sampleResidueBound = 9 := by
  native_decide

structure ResidueWindow where
  poleOrder : ℕ
  contourBudget : ℕ
  residueBudget : ℕ
  remainderBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ResidueWindow.poleReady (w : ResidueWindow) : Prop :=
  0 < w.poleOrder

def ResidueWindow.residueControlled (w : ResidueWindow) : Prop :=
  w.residueBudget + w.remainderBudget ≤ w.poleOrder * w.contourBudget + w.slack

def ResidueWindow.ready (w : ResidueWindow) : Prop :=
  w.poleReady ∧ w.residueControlled

def ResidueWindow.certificate (w : ResidueWindow) : ℕ :=
  w.poleOrder + w.contourBudget + w.residueBudget + w.remainderBudget + w.slack

theorem remainderBudget_le_certificate (w : ResidueWindow) :
    w.remainderBudget ≤ w.certificate := by
  unfold ResidueWindow.certificate
  omega

def sampleResidueWindow : ResidueWindow :=
  { poleOrder := 2, contourBudget := 7, residueBudget := 5, remainderBudget := 4, slack := 0 }

example : sampleResidueWindow.ready := by
  norm_num [sampleResidueWindow, ResidueWindow.ready,
    ResidueWindow.poleReady, ResidueWindow.residueControlled]


structure CauchyResidueBoundsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CauchyResidueBoundsBudgetCertificate.controlled
    (c : CauchyResidueBoundsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CauchyResidueBoundsBudgetCertificate.budgetControlled
    (c : CauchyResidueBoundsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CauchyResidueBoundsBudgetCertificate.Ready
    (c : CauchyResidueBoundsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CauchyResidueBoundsBudgetCertificate.size
    (c : CauchyResidueBoundsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cauchyResidueBounds_budgetCertificate_le_size
    (c : CauchyResidueBoundsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCauchyResidueBoundsBudgetCertificate :
    CauchyResidueBoundsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCauchyResidueBoundsBudgetCertificate.Ready := by
  constructor
  · norm_num [CauchyResidueBoundsBudgetCertificate.controlled,
      sampleCauchyResidueBoundsBudgetCertificate]
  · norm_num [CauchyResidueBoundsBudgetCertificate.budgetControlled,
      sampleCauchyResidueBoundsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCauchyResidueBoundsBudgetCertificate.certificateBudgetWindow ≤
      sampleCauchyResidueBoundsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCauchyResidueBoundsBudgetCertificate.Ready := by
  constructor
  · norm_num [CauchyResidueBoundsBudgetCertificate.controlled,
      sampleCauchyResidueBoundsBudgetCertificate]
  · norm_num [CauchyResidueBoundsBudgetCertificate.budgetControlled,
      sampleCauchyResidueBoundsBudgetCertificate]

example :
    sampleCauchyResidueBoundsBudgetCertificate.certificateBudgetWindow ≤
      sampleCauchyResidueBoundsBudgetCertificate.size := by
  apply cauchyResidueBounds_budgetCertificate_le_size
  constructor
  · norm_num [CauchyResidueBoundsBudgetCertificate.controlled,
      sampleCauchyResidueBoundsBudgetCertificate]
  · norm_num [CauchyResidueBoundsBudgetCertificate.budgetControlled,
      sampleCauchyResidueBoundsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CauchyResidueBoundsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCauchyResidueBoundsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCauchyResidueBoundsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.CauchyResidueBounds
