import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform residue bounds.

The finite schema records pole count, residue size, and contour slack for
uniform residue estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformResidueBounds

structure UniformResidueData where
  poleCount : ℕ
  residueBound : ℕ
  contourSlack : ℕ
deriving DecidableEq, Repr

def polesNonempty (d : UniformResidueData) : Prop :=
  0 < d.poleCount

def residueControlled (d : UniformResidueData) : Prop :=
  d.residueBound ≤ d.poleCount + d.contourSlack

def uniformResidueReady (d : UniformResidueData) : Prop :=
  polesNonempty d ∧ residueControlled d

def uniformResidueBudget (d : UniformResidueData) : ℕ :=
  d.poleCount + d.residueBound + d.contourSlack

theorem uniformResidueReady.poles {d : UniformResidueData}
    (h : uniformResidueReady d) :
    polesNonempty d ∧ residueControlled d ∧ d.residueBound ≤ uniformResidueBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformResidueBudget
  omega

theorem residueBound_le_uniformResidueBudget (d : UniformResidueData) :
    d.residueBound ≤ uniformResidueBudget d := by
  unfold uniformResidueBudget
  omega

def sampleUniformResidueData : UniformResidueData :=
  { poleCount := 3, residueBound := 8, contourSlack := 6 }

example : uniformResidueReady sampleUniformResidueData := by
  norm_num [uniformResidueReady, polesNonempty]
  norm_num [residueControlled, sampleUniformResidueData]

example : uniformResidueBudget sampleUniformResidueData = 17 := by
  native_decide

/-- Finite executable readiness audit for uniform residue data. -/
def uniformResidueDataListReady (data : List UniformResidueData) : Bool :=
  data.all fun d =>
    0 < d.poleCount && d.residueBound ≤ d.poleCount + d.contourSlack

theorem uniformResidueDataList_readyWindow :
    uniformResidueDataListReady
      [{ poleCount := 3, residueBound := 4, contourSlack := 1 },
       { poleCount := 3, residueBound := 8, contourSlack := 6 }] = true := by
  unfold uniformResidueDataListReady
  native_decide

structure UniformResidueCertificateWindow where
  poleWindow : ℕ
  residueWindow : ℕ
  contourSlack : ℕ
  residueBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformResidueCertificateWindow.residueControlled
    (w : UniformResidueCertificateWindow) : Prop :=
  w.residueWindow ≤ w.poleWindow + w.contourSlack + w.slack

def uniformResidueCertificateReady
    (w : UniformResidueCertificateWindow) : Prop :=
  0 < w.poleWindow ∧ w.residueControlled ∧
    w.residueBudget ≤ w.poleWindow + w.residueWindow + w.slack

def UniformResidueCertificateWindow.certificate
    (w : UniformResidueCertificateWindow) : ℕ :=
  w.poleWindow + w.residueWindow + w.contourSlack + w.residueBudget + w.slack

theorem uniformResidue_budget_le_certificate
    (w : UniformResidueCertificateWindow) :
    w.residueBudget ≤ w.certificate := by
  unfold UniformResidueCertificateWindow.certificate
  omega

def sampleUniformResidueCertificateWindow :
    UniformResidueCertificateWindow :=
  { poleWindow := 3, residueWindow := 8, contourSlack := 5,
    residueBudget := 12, slack := 1 }

example : uniformResidueCertificateReady
    sampleUniformResidueCertificateWindow := by
  norm_num [uniformResidueCertificateReady,
    UniformResidueCertificateWindow.residueControlled,
    sampleUniformResidueCertificateWindow]

structure UniformResidueRefinementCertificate where
  poleWindow : ℕ
  residueWindow : ℕ
  contourSlackWindow : ℕ
  residueBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformResidueRefinementCertificate.residueControlled
    (c : UniformResidueRefinementCertificate) : Prop :=
  c.residueWindow ≤ c.poleWindow + c.contourSlackWindow + c.slack

def UniformResidueRefinementCertificate.residueBudgetControlled
    (c : UniformResidueRefinementCertificate) : Prop :=
  c.residueBudgetWindow ≤
    c.poleWindow + c.residueWindow + c.contourSlackWindow + c.slack

def uniformResidueRefinementReady
    (c : UniformResidueRefinementCertificate) : Prop :=
  0 < c.poleWindow ∧
    c.residueControlled ∧
    c.residueBudgetControlled

def UniformResidueRefinementCertificate.size
    (c : UniformResidueRefinementCertificate) : ℕ :=
  c.poleWindow + c.residueWindow + c.contourSlackWindow + c.slack

theorem uniformResidue_residueBudgetWindow_le_size
    {c : UniformResidueRefinementCertificate}
    (h : uniformResidueRefinementReady c) :
    c.residueBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformResidueRefinementCertificate :
    UniformResidueRefinementCertificate :=
  { poleWindow := 3, residueWindow := 8, contourSlackWindow := 5,
    residueBudgetWindow := 12, slack := 1 }

example : uniformResidueRefinementReady
    sampleUniformResidueRefinementCertificate := by
  norm_num [uniformResidueRefinementReady,
    UniformResidueRefinementCertificate.residueControlled,
    UniformResidueRefinementCertificate.residueBudgetControlled,
    sampleUniformResidueRefinementCertificate]

example :
    sampleUniformResidueRefinementCertificate.residueBudgetWindow ≤
      sampleUniformResidueRefinementCertificate.size := by
  norm_num [UniformResidueRefinementCertificate.size,
    sampleUniformResidueRefinementCertificate]

/-- A second-stage certificate with the uniform-residue budget separated from size. -/
structure UniformResidueBudgetCertificate where
  poleWindow : ℕ
  residueWindow : ℕ
  contourSlackWindow : ℕ
  residueBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformResidueBudgetCertificate.residueControlled
    (cert : UniformResidueBudgetCertificate) : Prop :=
  0 < cert.poleWindow ∧
    cert.residueWindow ≤ cert.poleWindow + cert.contourSlackWindow + cert.slack ∧
      cert.residueBudgetWindow ≤
        cert.poleWindow + cert.residueWindow + cert.contourSlackWindow + cert.slack

def UniformResidueBudgetCertificate.budgetControlled
    (cert : UniformResidueBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.poleWindow + cert.residueWindow + cert.contourSlackWindow +
      cert.residueBudgetWindow + cert.slack

def uniformResidueBudgetReady (cert : UniformResidueBudgetCertificate) : Prop :=
  cert.residueControlled ∧ cert.budgetControlled

def UniformResidueBudgetCertificate.size
    (cert : UniformResidueBudgetCertificate) : ℕ :=
  cert.poleWindow + cert.residueWindow + cert.contourSlackWindow +
    cert.residueBudgetWindow + cert.slack

theorem uniformResidue_certificateBudgetWindow_le_size
    (cert : UniformResidueBudgetCertificate)
    (h : uniformResidueBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformResidueBudgetCertificate :
    UniformResidueBudgetCertificate :=
  { poleWindow := 3, residueWindow := 8, contourSlackWindow := 5,
    residueBudgetWindow := 12, certificateBudgetWindow := 29, slack := 1 }

example : uniformResidueBudgetReady sampleUniformResidueBudgetCertificate := by
  norm_num [uniformResidueBudgetReady,
    UniformResidueBudgetCertificate.residueControlled,
    UniformResidueBudgetCertificate.budgetControlled,
    sampleUniformResidueBudgetCertificate]

example :
    sampleUniformResidueBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformResidueBudgetCertificate.size := by
  apply uniformResidue_certificateBudgetWindow_le_size
  norm_num [uniformResidueBudgetReady,
    UniformResidueBudgetCertificate.residueControlled,
    UniformResidueBudgetCertificate.budgetControlled,
    sampleUniformResidueBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    uniformResidueBudgetReady sampleUniformResidueBudgetCertificate := by
  constructor
  · norm_num [UniformResidueBudgetCertificate.residueControlled,
      sampleUniformResidueBudgetCertificate]
  · norm_num [UniformResidueBudgetCertificate.budgetControlled,
      sampleUniformResidueBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformResidueBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformResidueBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformResidueBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformResidueBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformResidueBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformResidueBounds
