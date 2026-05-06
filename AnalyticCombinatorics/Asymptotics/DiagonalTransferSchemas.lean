import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Diagonal transfer bookkeeping for bivariate generating functions.

The module records finite balance checks for diagonal coefficient
extraction before analytic estimates are applied.
-/

namespace AnalyticCombinatorics.Asymptotics.DiagonalTransferSchemas

structure DiagonalData where
  rowIndex : ℕ
  colIndex : ℕ
  scale : ℕ
deriving DecidableEq, Repr

def onDiagonal (d : DiagonalData) : Prop :=
  d.rowIndex = d.colIndex

def diagonalReady (d : DiagonalData) : Prop :=
  onDiagonal d ∧ 0 < d.scale

def shiftedDiagonal (offset n : ℕ) : DiagonalData :=
  { rowIndex := n + offset, colIndex := n + offset, scale := n + 1 }

theorem shiftedDiagonal_onDiagonal (offset n : ℕ) :
    onDiagonal (shiftedDiagonal offset n) := by
  rfl

theorem shiftedDiagonal_ready (offset n : ℕ) :
    diagonalReady (shiftedDiagonal offset n) := by
  unfold diagonalReady
  constructor
  · rfl
  · simp [shiftedDiagonal]

example : (shiftedDiagonal 2 5).rowIndex = 7 := by
  native_decide

example : diagonalReady (shiftedDiagonal 2 5) := by
  exact shiftedDiagonal_ready 2 5

/-- Finite executable readiness audit for diagonal transfer data. -/
def diagonalDataListReady (data : List DiagonalData) : Bool :=
  data.all fun d => d.rowIndex == d.colIndex && 0 < d.scale

theorem diagonalDataList_readyWindow :
    diagonalDataListReady
      [{ rowIndex := 3, colIndex := 3, scale := 1 },
       { rowIndex := 7, colIndex := 7, scale := 6 }] = true := by
  unfold diagonalDataListReady
  native_decide

structure DiagonalTransferWindow where
  rowIndex : ℕ
  colIndex : ℕ
  diagonalMass : ℕ
  offDiagonalSlack : ℕ
deriving DecidableEq, Repr

def DiagonalTransferWindow.onMainDiagonal (w : DiagonalTransferWindow) : Prop :=
  w.rowIndex = w.colIndex

def DiagonalTransferWindow.massControlled (w : DiagonalTransferWindow) : Prop :=
  w.diagonalMass ≤ w.rowIndex + w.colIndex + w.offDiagonalSlack

def DiagonalTransferWindow.ready (w : DiagonalTransferWindow) : Prop :=
  w.onMainDiagonal ∧ w.massControlled

def DiagonalTransferWindow.certificate (w : DiagonalTransferWindow) : ℕ :=
  w.rowIndex + w.colIndex + w.diagonalMass + w.offDiagonalSlack

theorem diagonalMass_le_certificate (w : DiagonalTransferWindow) :
    w.diagonalMass ≤ w.certificate := by
  unfold DiagonalTransferWindow.certificate
  omega

def sampleDiagonalTransferWindow : DiagonalTransferWindow :=
  { rowIndex := 4, colIndex := 4, diagonalMass := 7, offDiagonalSlack := 0 }

example : sampleDiagonalTransferWindow.ready := by
  norm_num [sampleDiagonalTransferWindow, DiagonalTransferWindow.ready,
    DiagonalTransferWindow.onMainDiagonal, DiagonalTransferWindow.massControlled]

/-- A refinement certificate for diagonal transfer windows. -/
structure DiagonalTransferCertificate where
  rowWindow : ℕ
  colWindow : ℕ
  diagonalMassWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Diagonal certificates keep row and column windows balanced. -/
def diagonalTransferCertificateControlled
    (w : DiagonalTransferCertificate) : Prop :=
  w.rowWindow = w.colWindow ∧
    w.diagonalMassWindow ≤ w.rowWindow + w.colWindow + w.slack

/-- Readiness for a diagonal transfer certificate. -/
def diagonalTransferCertificateReady
    (w : DiagonalTransferCertificate) : Prop :=
  diagonalTransferCertificateControlled w ∧
    w.certificateBudget ≤ w.rowWindow + w.diagonalMassWindow + w.slack

/-- Total size of a diagonal transfer certificate. -/
def diagonalTransferCertificateSize
    (w : DiagonalTransferCertificate) : ℕ :=
  w.rowWindow + w.colWindow + w.diagonalMassWindow +
    w.certificateBudget + w.slack

theorem diagonalTransferCertificate_budget_le_size
    (w : DiagonalTransferCertificate)
    (h : diagonalTransferCertificateReady w) :
    w.certificateBudget ≤ diagonalTransferCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold diagonalTransferCertificateSize
  omega

def sampleDiagonalTransferCertificate : DiagonalTransferCertificate where
  rowWindow := 4
  colWindow := 4
  diagonalMassWindow := 7
  certificateBudget := 11
  slack := 0

example :
    diagonalTransferCertificateReady sampleDiagonalTransferCertificate := by
  norm_num [diagonalTransferCertificateReady,
    diagonalTransferCertificateControlled, sampleDiagonalTransferCertificate]

example :
    sampleDiagonalTransferCertificate.certificateBudget ≤
      diagonalTransferCertificateSize sampleDiagonalTransferCertificate := by
  apply diagonalTransferCertificate_budget_le_size
  norm_num [diagonalTransferCertificateReady,
    diagonalTransferCertificateControlled, sampleDiagonalTransferCertificate]

/-- A refinement certificate with the diagonal budget separated from size. -/
structure DiagonalTransferRefinementCertificate where
  rowWindow : ℕ
  colWindow : ℕ
  diagonalMassWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def DiagonalTransferRefinementCertificate.diagonalControlled
    (cert : DiagonalTransferRefinementCertificate) : Prop :=
  cert.rowWindow = cert.colWindow ∧
    cert.diagonalMassWindow ≤ cert.rowWindow + cert.colWindow + cert.slack

def DiagonalTransferRefinementCertificate.budgetControlled
    (cert : DiagonalTransferRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.rowWindow + cert.colWindow + cert.diagonalMassWindow + cert.slack

def diagonalTransferRefinementReady
    (cert : DiagonalTransferRefinementCertificate) : Prop :=
  cert.diagonalControlled ∧ cert.budgetControlled

def DiagonalTransferRefinementCertificate.size
    (cert : DiagonalTransferRefinementCertificate) : ℕ :=
  cert.rowWindow + cert.colWindow + cert.diagonalMassWindow + cert.slack

theorem diagonalTransfer_certificateBudgetWindow_le_size
    (cert : DiagonalTransferRefinementCertificate)
    (h : diagonalTransferRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDiagonalTransferRefinementCertificate :
    DiagonalTransferRefinementCertificate where
  rowWindow := 4
  colWindow := 4
  diagonalMassWindow := 7
  certificateBudgetWindow := 15
  slack := 0

example :
    diagonalTransferRefinementReady sampleDiagonalTransferRefinementCertificate := by
  norm_num [diagonalTransferRefinementReady,
    DiagonalTransferRefinementCertificate.diagonalControlled,
    DiagonalTransferRefinementCertificate.budgetControlled,
    sampleDiagonalTransferRefinementCertificate]

example :
    sampleDiagonalTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleDiagonalTransferRefinementCertificate.size := by
  apply diagonalTransfer_certificateBudgetWindow_le_size
  norm_num [diagonalTransferRefinementReady,
    DiagonalTransferRefinementCertificate.diagonalControlled,
    DiagonalTransferRefinementCertificate.budgetControlled,
    sampleDiagonalTransferRefinementCertificate]

structure DiagonalTransferBudgetCertificate where
  rowWindow : ℕ
  colWindow : ℕ
  diagonalMassWindow : ℕ
  diagonalBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DiagonalTransferBudgetCertificate.controlled
    (c : DiagonalTransferBudgetCertificate) : Prop :=
  c.rowWindow = c.colWindow ∧
    c.diagonalMassWindow ≤ c.rowWindow + c.colWindow + c.slack ∧
      c.diagonalBudgetWindow ≤
        c.rowWindow + c.colWindow + c.diagonalMassWindow + c.slack

def DiagonalTransferBudgetCertificate.budgetControlled
    (c : DiagonalTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.rowWindow + c.colWindow + c.diagonalMassWindow +
      c.diagonalBudgetWindow + c.slack

def DiagonalTransferBudgetCertificate.Ready
    (c : DiagonalTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DiagonalTransferBudgetCertificate.size
    (c : DiagonalTransferBudgetCertificate) : ℕ :=
  c.rowWindow + c.colWindow + c.diagonalMassWindow +
    c.diagonalBudgetWindow + c.slack

theorem diagonalTransfer_budgetCertificate_le_size
    (c : DiagonalTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDiagonalTransferBudgetCertificate :
    DiagonalTransferBudgetCertificate :=
  { rowWindow := 4
    colWindow := 4
    diagonalMassWindow := 7
    diagonalBudgetWindow := 15
    certificateBudgetWindow := 30
    slack := 0 }

example : sampleDiagonalTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [DiagonalTransferBudgetCertificate.controlled,
      sampleDiagonalTransferBudgetCertificate]
  · norm_num [DiagonalTransferBudgetCertificate.budgetControlled,
      sampleDiagonalTransferBudgetCertificate]

example :
    sampleDiagonalTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleDiagonalTransferBudgetCertificate.size := by
  apply diagonalTransfer_budgetCertificate_le_size
  constructor
  · norm_num [DiagonalTransferBudgetCertificate.controlled,
      sampleDiagonalTransferBudgetCertificate]
  · norm_num [DiagonalTransferBudgetCertificate.budgetControlled,
      sampleDiagonalTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDiagonalTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [DiagonalTransferBudgetCertificate.controlled,
      sampleDiagonalTransferBudgetCertificate]
  · norm_num [DiagonalTransferBudgetCertificate.budgetControlled,
      sampleDiagonalTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDiagonalTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleDiagonalTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List DiagonalTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDiagonalTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleDiagonalTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.DiagonalTransferSchemas
