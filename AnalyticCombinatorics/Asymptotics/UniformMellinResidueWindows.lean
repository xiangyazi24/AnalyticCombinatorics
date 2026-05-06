import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Mellin residue windows.

This module records finite bookkeeping for Mellin residue windows.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformMellinResidueWindows

structure MellinResidueWindowData where
  residueOrder : ℕ
  stripWindow : ℕ
  uniformSlack : ℕ
deriving DecidableEq, Repr

def hasResidueOrder (d : MellinResidueWindowData) : Prop :=
  0 < d.residueOrder

def stripWindowControlled (d : MellinResidueWindowData) : Prop :=
  d.stripWindow ≤ d.residueOrder + d.uniformSlack

def mellinResidueWindowReady (d : MellinResidueWindowData) : Prop :=
  hasResidueOrder d ∧ stripWindowControlled d

def mellinResidueWindowBudget (d : MellinResidueWindowData) : ℕ :=
  d.residueOrder + d.stripWindow + d.uniformSlack

theorem mellinResidueWindowReady.hasResidueOrder
    {d : MellinResidueWindowData}
    (h : mellinResidueWindowReady d) :
    hasResidueOrder d ∧ stripWindowControlled d ∧
      d.stripWindow ≤ mellinResidueWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold mellinResidueWindowBudget
  omega

theorem stripWindow_le_budget (d : MellinResidueWindowData) :
    d.stripWindow ≤ mellinResidueWindowBudget d := by
  unfold mellinResidueWindowBudget
  omega

def sampleMellinResidueWindowData : MellinResidueWindowData :=
  { residueOrder := 6, stripWindow := 8, uniformSlack := 3 }

example : mellinResidueWindowReady sampleMellinResidueWindowData := by
  norm_num [mellinResidueWindowReady, hasResidueOrder]
  norm_num [stripWindowControlled, sampleMellinResidueWindowData]

example : mellinResidueWindowBudget sampleMellinResidueWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for Mellin residue windows. -/
def mellinResidueWindowDataListReady
    (data : List MellinResidueWindowData) : Bool :=
  data.all fun d =>
    0 < d.residueOrder && d.stripWindow ≤ d.residueOrder + d.uniformSlack

theorem mellinResidueWindowDataList_readyWindow :
    mellinResidueWindowDataListReady
      [{ residueOrder := 4, stripWindow := 5, uniformSlack := 1 },
       { residueOrder := 6, stripWindow := 8, uniformSlack := 3 }] = true := by
  unfold mellinResidueWindowDataListReady
  native_decide

/-- A certificate window for uniform Mellin residues. -/
structure MellinResidueCertificateWindow where
  residueWindow : ℕ
  stripWindow : ℕ
  uniformSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The strip window is controlled by residue order and slack. -/
def mellinResidueCertificateControlled
    (w : MellinResidueCertificateWindow) : Prop :=
  w.stripWindow ≤ w.residueWindow + w.uniformSlack + w.slack

/-- Readiness for a Mellin residue certificate. -/
def mellinResidueCertificateReady
    (w : MellinResidueCertificateWindow) : Prop :=
  0 < w.residueWindow ∧
    mellinResidueCertificateControlled w ∧
      w.certificateBudget ≤ w.residueWindow + w.stripWindow + w.slack

/-- Total size of a Mellin residue certificate. -/
def mellinResidueCertificate (w : MellinResidueCertificateWindow) : ℕ :=
  w.residueWindow + w.stripWindow + w.uniformSlack + w.certificateBudget + w.slack

theorem mellinResidueCertificate_budget_le_certificate
    (w : MellinResidueCertificateWindow)
    (h : mellinResidueCertificateReady w) :
    w.certificateBudget ≤ mellinResidueCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold mellinResidueCertificate
  omega

def sampleMellinResidueCertificateWindow :
    MellinResidueCertificateWindow where
  residueWindow := 6
  stripWindow := 7
  uniformSlack := 2
  certificateBudget := 12
  slack := 1

example :
    mellinResidueCertificateReady sampleMellinResidueCertificateWindow := by
  norm_num [mellinResidueCertificateReady,
    mellinResidueCertificateControlled, sampleMellinResidueCertificateWindow]

example :
    sampleMellinResidueCertificateWindow.certificateBudget ≤
      mellinResidueCertificate sampleMellinResidueCertificateWindow := by
  apply mellinResidueCertificate_budget_le_certificate
  norm_num [mellinResidueCertificateReady,
    mellinResidueCertificateControlled, sampleMellinResidueCertificateWindow]

structure MellinResidueRefinementCertificate where
  residueWindow : ℕ
  stripWindow : ℕ
  uniformSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinResidueRefinementCertificate.stripControlled
    (c : MellinResidueRefinementCertificate) : Prop :=
  c.stripWindow ≤ c.residueWindow + c.uniformSlackWindow + c.slack

def MellinResidueRefinementCertificate.certificateBudgetControlled
    (c : MellinResidueRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.residueWindow + c.stripWindow + c.uniformSlackWindow + c.slack

def mellinResidueRefinementReady
    (c : MellinResidueRefinementCertificate) : Prop :=
  0 < c.residueWindow ∧ c.stripControlled ∧ c.certificateBudgetControlled

def MellinResidueRefinementCertificate.size
    (c : MellinResidueRefinementCertificate) : ℕ :=
  c.residueWindow + c.stripWindow + c.uniformSlackWindow + c.slack

theorem mellinResidue_certificateBudgetWindow_le_size
    {c : MellinResidueRefinementCertificate}
    (h : mellinResidueRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleMellinResidueRefinementCertificate :
    MellinResidueRefinementCertificate :=
  { residueWindow := 6, stripWindow := 7, uniformSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : mellinResidueRefinementReady
    sampleMellinResidueRefinementCertificate := by
  norm_num [mellinResidueRefinementReady,
    MellinResidueRefinementCertificate.stripControlled,
    MellinResidueRefinementCertificate.certificateBudgetControlled,
    sampleMellinResidueRefinementCertificate]

example :
    sampleMellinResidueRefinementCertificate.certificateBudgetWindow ≤
      sampleMellinResidueRefinementCertificate.size := by
  norm_num [MellinResidueRefinementCertificate.size,
    sampleMellinResidueRefinementCertificate]

/-- A second-stage Mellin residue certificate with a named external budget. -/
structure MellinResidueBudgetCertificate where
  residueWindow : ℕ
  stripWindow : ℕ
  uniformSlackWindow : ℕ
  residueBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinResidueBudgetCertificate.residueControlled
    (cert : MellinResidueBudgetCertificate) : Prop :=
  0 < cert.residueWindow ∧
    cert.stripWindow ≤ cert.residueWindow + cert.uniformSlackWindow + cert.slack ∧
      cert.residueBudgetWindow ≤
        cert.residueWindow + cert.stripWindow + cert.uniformSlackWindow + cert.slack

def MellinResidueBudgetCertificate.budgetControlled
    (cert : MellinResidueBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.residueWindow + cert.stripWindow + cert.uniformSlackWindow +
      cert.residueBudgetWindow + cert.slack

def mellinResidueBudgetReady (cert : MellinResidueBudgetCertificate) : Prop :=
  cert.residueControlled ∧ cert.budgetControlled

def MellinResidueBudgetCertificate.size
    (cert : MellinResidueBudgetCertificate) : ℕ :=
  cert.residueWindow + cert.stripWindow + cert.uniformSlackWindow +
    cert.residueBudgetWindow + cert.slack

theorem mellinResidue_budgetCertificate_le_size
    (cert : MellinResidueBudgetCertificate)
    (h : mellinResidueBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMellinResidueBudgetCertificate :
    MellinResidueBudgetCertificate :=
  { residueWindow := 6, stripWindow := 7, uniformSlackWindow := 2,
    residueBudgetWindow := 16, certificateBudgetWindow := 32, slack := 1 }

example : mellinResidueBudgetReady sampleMellinResidueBudgetCertificate := by
  norm_num [mellinResidueBudgetReady,
    MellinResidueBudgetCertificate.residueControlled,
    MellinResidueBudgetCertificate.budgetControlled,
    sampleMellinResidueBudgetCertificate]

example :
    sampleMellinResidueBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinResidueBudgetCertificate.size := by
  apply mellinResidue_budgetCertificate_le_size
  norm_num [mellinResidueBudgetReady,
    MellinResidueBudgetCertificate.residueControlled,
    MellinResidueBudgetCertificate.budgetControlled,
    sampleMellinResidueBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    mellinResidueBudgetReady sampleMellinResidueBudgetCertificate := by
  constructor
  · norm_num [MellinResidueBudgetCertificate.residueControlled,
      sampleMellinResidueBudgetCertificate]
  · norm_num [MellinResidueBudgetCertificate.budgetControlled,
      sampleMellinResidueBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMellinResidueBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinResidueBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MellinResidueBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMellinResidueBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleMellinResidueBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformMellinResidueWindows
