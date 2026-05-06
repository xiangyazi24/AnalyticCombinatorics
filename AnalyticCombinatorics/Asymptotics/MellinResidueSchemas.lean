import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Mellin residue schemas.

The finite schema records pole order, strip width, and residue slack for
Mellin residue expansions.
-/

namespace AnalyticCombinatorics.Asymptotics.MellinResidueSchemas

structure MellinResidueData where
  poleOrder : ℕ
  stripWidth : ℕ
  residueSlack : ℕ
deriving DecidableEq, Repr

def poleOrderPositive (d : MellinResidueData) : Prop :=
  0 < d.poleOrder

def stripControlled (d : MellinResidueData) : Prop :=
  d.stripWidth ≤ d.poleOrder + d.residueSlack

def mellinResidueReady (d : MellinResidueData) : Prop :=
  poleOrderPositive d ∧ stripControlled d

def mellinResidueBudget (d : MellinResidueData) : ℕ :=
  d.poleOrder + d.stripWidth + d.residueSlack

theorem mellinResidueReady.pole {d : MellinResidueData}
    (h : mellinResidueReady d) :
    poleOrderPositive d ∧ stripControlled d ∧ d.stripWidth ≤ mellinResidueBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold mellinResidueBudget
  omega

theorem stripWidth_le_mellinResidueBudget (d : MellinResidueData) :
    d.stripWidth ≤ mellinResidueBudget d := by
  unfold mellinResidueBudget
  omega

def sampleMellinResidueData : MellinResidueData :=
  { poleOrder := 3, stripWidth := 6, residueSlack := 4 }

example : mellinResidueReady sampleMellinResidueData := by
  norm_num [mellinResidueReady, poleOrderPositive]
  norm_num [stripControlled, sampleMellinResidueData]

example : mellinResidueBudget sampleMellinResidueData = 13 := by
  native_decide

/-- Finite executable readiness audit for Mellin residue data. -/
def mellinResidueDataListReady (data : List MellinResidueData) : Bool :=
  data.all fun d => 0 < d.poleOrder && d.stripWidth ≤ d.poleOrder + d.residueSlack

theorem mellinResidueDataList_readyWindow :
    mellinResidueDataListReady
      [{ poleOrder := 2, stripWidth := 3, residueSlack := 1 },
       { poleOrder := 3, stripWidth := 6, residueSlack := 4 }] = true := by
  unfold mellinResidueDataListReady
  native_decide

structure MellinResidueWindow where
  poleWindow : ℕ
  stripWindow : ℕ
  residueSlack : ℕ
  residueBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinResidueWindow.stripControlled (w : MellinResidueWindow) : Prop :=
  w.stripWindow ≤ w.poleWindow + w.residueSlack + w.slack

def mellinResidueWindowReady (w : MellinResidueWindow) : Prop :=
  0 < w.poleWindow ∧ w.stripControlled ∧
    w.residueBudget ≤ w.poleWindow + w.stripWindow + w.slack

def MellinResidueWindow.certificate (w : MellinResidueWindow) : ℕ :=
  w.poleWindow + w.stripWindow + w.residueSlack + w.residueBudget + w.slack

theorem mellinResidue_residueBudget_le_certificate
    (w : MellinResidueWindow) :
    w.residueBudget ≤ w.certificate := by
  unfold MellinResidueWindow.certificate
  omega

def sampleMellinResidueWindow : MellinResidueWindow :=
  { poleWindow := 3, stripWindow := 6, residueSlack := 3, residueBudget := 10, slack := 1 }

example : mellinResidueWindowReady sampleMellinResidueWindow := by
  norm_num [mellinResidueWindowReady, MellinResidueWindow.stripControlled,
    sampleMellinResidueWindow]

/-- A refinement certificate for Mellin residue windows. -/
structure MellinResidueCertificate where
  poleWindow : ℕ
  stripWindow : ℕ
  residueSlackWindow : ℕ
  residueBudgetWindow : ℕ
  slack : ℕ

/-- Strip and residue budgets are controlled by pole order and slack. -/
def mellinResidueCertificateControlled
    (w : MellinResidueCertificate) : Prop :=
  0 < w.poleWindow ∧
    w.stripWindow ≤ w.poleWindow + w.residueSlackWindow + w.slack ∧
      w.residueBudgetWindow ≤ w.poleWindow + w.stripWindow + w.slack

/-- Readiness for a Mellin residue certificate. -/
def mellinResidueCertificateReady
    (w : MellinResidueCertificate) : Prop :=
  mellinResidueCertificateControlled w ∧
    w.residueBudgetWindow ≤
      w.poleWindow + w.stripWindow + w.residueSlackWindow +
        w.residueBudgetWindow + w.slack

/-- Total size of a Mellin residue certificate. -/
def mellinResidueCertificateSize (w : MellinResidueCertificate) : ℕ :=
  w.poleWindow + w.stripWindow + w.residueSlackWindow +
    w.residueBudgetWindow + w.slack

theorem mellinResidueCertificate_budget_le_size
    (w : MellinResidueCertificate)
    (h : mellinResidueCertificateReady w) :
    w.residueBudgetWindow ≤ mellinResidueCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold mellinResidueCertificateSize
  omega

def sampleMellinResidueCertificate : MellinResidueCertificate where
  poleWindow := 3
  stripWindow := 6
  residueSlackWindow := 3
  residueBudgetWindow := 10
  slack := 1

example :
    mellinResidueCertificateReady sampleMellinResidueCertificate := by
  norm_num [mellinResidueCertificateReady,
    mellinResidueCertificateControlled, sampleMellinResidueCertificate]

example :
    sampleMellinResidueCertificate.residueBudgetWindow ≤
      mellinResidueCertificateSize sampleMellinResidueCertificate := by
  apply mellinResidueCertificate_budget_le_size
  norm_num [mellinResidueCertificateReady,
    mellinResidueCertificateControlled, sampleMellinResidueCertificate]

/-- A refinement certificate with the Mellin-residue budget separated from size. -/
structure MellinResidueRefinementCertificate where
  poleWindow : ℕ
  stripWindow : ℕ
  residueSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinResidueRefinementCertificate.stripControlled
    (cert : MellinResidueRefinementCertificate) : Prop :=
  0 < cert.poleWindow ∧
    cert.stripWindow ≤ cert.poleWindow + cert.residueSlackWindow + cert.slack

def MellinResidueRefinementCertificate.budgetControlled
    (cert : MellinResidueRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.poleWindow + cert.stripWindow + cert.residueSlackWindow + cert.slack

def mellinResidueRefinementReady
    (cert : MellinResidueRefinementCertificate) : Prop :=
  cert.stripControlled ∧ cert.budgetControlled

def MellinResidueRefinementCertificate.size
    (cert : MellinResidueRefinementCertificate) : ℕ :=
  cert.poleWindow + cert.stripWindow + cert.residueSlackWindow + cert.slack

theorem mellinResidue_certificateBudgetWindow_le_size
    (cert : MellinResidueRefinementCertificate)
    (h : mellinResidueRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMellinResidueRefinementCertificate :
    MellinResidueRefinementCertificate :=
  { poleWindow := 3, stripWindow := 6, residueSlackWindow := 3,
    certificateBudgetWindow := 13, slack := 1 }

example :
    mellinResidueRefinementReady sampleMellinResidueRefinementCertificate := by
  norm_num [mellinResidueRefinementReady,
    MellinResidueRefinementCertificate.stripControlled,
    MellinResidueRefinementCertificate.budgetControlled,
    sampleMellinResidueRefinementCertificate]

example :
    sampleMellinResidueRefinementCertificate.certificateBudgetWindow ≤
      sampleMellinResidueRefinementCertificate.size := by
  apply mellinResidue_certificateBudgetWindow_le_size
  norm_num [mellinResidueRefinementReady,
    MellinResidueRefinementCertificate.stripControlled,
    MellinResidueRefinementCertificate.budgetControlled,
    sampleMellinResidueRefinementCertificate]


structure MellinResidueSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinResidueSchemasBudgetCertificate.controlled
    (c : MellinResidueSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def MellinResidueSchemasBudgetCertificate.budgetControlled
    (c : MellinResidueSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MellinResidueSchemasBudgetCertificate.Ready
    (c : MellinResidueSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MellinResidueSchemasBudgetCertificate.size
    (c : MellinResidueSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem mellinResidueSchemas_budgetCertificate_le_size
    (c : MellinResidueSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMellinResidueSchemasBudgetCertificate :
    MellinResidueSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleMellinResidueSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinResidueSchemasBudgetCertificate.controlled,
      sampleMellinResidueSchemasBudgetCertificate]
  · norm_num [MellinResidueSchemasBudgetCertificate.budgetControlled,
      sampleMellinResidueSchemasBudgetCertificate]

example :
    sampleMellinResidueSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinResidueSchemasBudgetCertificate.size := by
  apply mellinResidueSchemas_budgetCertificate_le_size
  constructor
  · norm_num [MellinResidueSchemasBudgetCertificate.controlled,
      sampleMellinResidueSchemasBudgetCertificate]
  · norm_num [MellinResidueSchemasBudgetCertificate.budgetControlled,
      sampleMellinResidueSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMellinResidueSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinResidueSchemasBudgetCertificate.controlled,
      sampleMellinResidueSchemasBudgetCertificate]
  · norm_num [MellinResidueSchemasBudgetCertificate.budgetControlled,
      sampleMellinResidueSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMellinResidueSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinResidueSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MellinResidueSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMellinResidueSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleMellinResidueSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.MellinResidueSchemas
