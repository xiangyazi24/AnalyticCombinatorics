import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Rouche window models.

This module records finite bookkeeping for Rouche comparison windows.
-/

namespace AnalyticCombinatorics.AppB.UniformRoucheWindowModels

structure RoucheWindowData where
  contourPieces : ℕ
  comparisonWindow : ℕ
  roucheSlack : ℕ
deriving DecidableEq, Repr

def hasContourPieces (d : RoucheWindowData) : Prop :=
  0 < d.contourPieces

def comparisonWindowControlled (d : RoucheWindowData) : Prop :=
  d.comparisonWindow ≤ d.contourPieces + d.roucheSlack

def roucheWindowReady (d : RoucheWindowData) : Prop :=
  hasContourPieces d ∧ comparisonWindowControlled d

def roucheWindowBudget (d : RoucheWindowData) : ℕ :=
  d.contourPieces + d.comparisonWindow + d.roucheSlack

theorem roucheWindowReady.hasContourPieces {d : RoucheWindowData}
    (h : roucheWindowReady d) :
    hasContourPieces d ∧ comparisonWindowControlled d ∧
      d.comparisonWindow ≤ roucheWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold roucheWindowBudget
  omega

theorem comparisonWindow_le_budget (d : RoucheWindowData) :
    d.comparisonWindow ≤ roucheWindowBudget d := by
  unfold roucheWindowBudget
  omega

def sampleRoucheWindowData : RoucheWindowData :=
  { contourPieces := 6, comparisonWindow := 8, roucheSlack := 3 }

example : roucheWindowReady sampleRoucheWindowData := by
  norm_num [roucheWindowReady, hasContourPieces]
  norm_num [comparisonWindowControlled, sampleRoucheWindowData]

example : roucheWindowBudget sampleRoucheWindowData = 17 := by
  native_decide

structure UniformRoucheWindow where
  contourWindow : ℕ
  comparisonWindow : ℕ
  roucheSlack : ℕ
  comparisonBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformRoucheWindow.comparisonControlled (w : UniformRoucheWindow) : Prop :=
  w.comparisonWindow ≤ w.contourWindow + w.roucheSlack + w.slack

def uniformRoucheWindowReady (w : UniformRoucheWindow) : Prop :=
  0 < w.contourWindow ∧ w.comparisonControlled ∧
    w.comparisonBudget ≤ w.contourWindow + w.comparisonWindow + w.slack

def UniformRoucheWindow.certificate (w : UniformRoucheWindow) : ℕ :=
  w.contourWindow + w.comparisonWindow + w.roucheSlack + w.comparisonBudget + w.slack

theorem uniformRouche_comparisonBudget_le_certificate (w : UniformRoucheWindow) :
    w.comparisonBudget ≤ w.certificate := by
  unfold UniformRoucheWindow.certificate
  omega

def sampleUniformRoucheWindow : UniformRoucheWindow :=
  { contourWindow := 5, comparisonWindow := 7, roucheSlack := 2,
    comparisonBudget := 14, slack := 2 }

example : uniformRoucheWindowReady sampleUniformRoucheWindow := by
  norm_num [uniformRoucheWindowReady, UniformRoucheWindow.comparisonControlled,
    sampleUniformRoucheWindow]


structure UniformRoucheWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformRoucheWindowModelsBudgetCertificate.controlled
    (c : UniformRoucheWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformRoucheWindowModelsBudgetCertificate.budgetControlled
    (c : UniformRoucheWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformRoucheWindowModelsBudgetCertificate.Ready
    (c : UniformRoucheWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformRoucheWindowModelsBudgetCertificate.size
    (c : UniformRoucheWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformRoucheWindowModels_budgetCertificate_le_size
    (c : UniformRoucheWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformRoucheWindowModelsBudgetCertificate :
    UniformRoucheWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformRoucheWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformRoucheWindowModelsBudgetCertificate.controlled,
      sampleUniformRoucheWindowModelsBudgetCertificate]
  · norm_num [UniformRoucheWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformRoucheWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformRoucheWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformRoucheWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformRoucheWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformRoucheWindowModelsBudgetCertificate.controlled,
      sampleUniformRoucheWindowModelsBudgetCertificate]
  · norm_num [UniformRoucheWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformRoucheWindowModelsBudgetCertificate]

example :
    sampleUniformRoucheWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformRoucheWindowModelsBudgetCertificate.size := by
  apply uniformRoucheWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformRoucheWindowModelsBudgetCertificate.controlled,
      sampleUniformRoucheWindowModelsBudgetCertificate]
  · norm_num [UniformRoucheWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformRoucheWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformRoucheWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformRoucheWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformRoucheWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformRoucheWindowModels
