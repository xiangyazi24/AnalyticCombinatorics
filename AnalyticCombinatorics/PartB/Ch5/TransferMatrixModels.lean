import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Transfer matrix models.

Finite matrix-size and path-depth bookkeeping for rational generating
functions derived from transfer matrices.
-/

namespace AnalyticCombinatorics.PartB.Ch5.TransferMatrixModels

/-- Two-state transfer matrix for binary words with no consecutive ones. -/
def noConsecutiveOnesStep (src dst : Fin 2) : ℕ :=
  match src.val, dst.val with
  | 0, 0 => 1
  | 0, 1 => 1
  | 1, 0 => 1
  | _, _ => 0

/-- One-step row sum for a finite transfer matrix. -/
def rowSum2 (step : Fin 2 → Fin 2 → ℕ) (src : Fin 2) : ℕ :=
  (List.finRange 2).foldl (fun total dst => total + step src dst) 0

/-- Finite audit for bounded row sums of a transfer matrix. -/
def transferRowBoundCheck (step : Fin 2 → Fin 2 → ℕ) (bound : ℕ) : Bool :=
  (List.finRange 2).all fun src => rowSum2 step src ≤ bound

theorem noConsecutiveOnes_rowBound :
    transferRowBoundCheck noConsecutiveOnesStep 2 = true := by
  unfold transferRowBoundCheck rowSum2 noConsecutiveOnesStep
  native_decide

/-- Total one-step weight of a two-state transfer matrix. -/
def totalStepWeight2 (step : Fin 2 → Fin 2 → ℕ) : ℕ :=
  (List.finRange 2).foldl (fun total src => total + rowSum2 step src) 0

theorem noConsecutiveOnes_totalStepWeight :
    totalStepWeight2 noConsecutiveOnesStep = 3 := by
  unfold totalStepWeight2 rowSum2 noConsecutiveOnesStep
  native_decide

structure TransferMatrixWindow where
  matrixSize : ℕ
  nonzeroEntryWindow : ℕ
  pathDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def transferMatrixReady (w : TransferMatrixWindow) : Prop :=
  0 < w.matrixSize ∧ w.pathDepth ≤ w.matrixSize + w.nonzeroEntryWindow + w.slack

def transferMatrixBudget (w : TransferMatrixWindow) : ℕ :=
  w.matrixSize + w.nonzeroEntryWindow + w.pathDepth + w.slack

theorem pathDepth_le_transferMatrixBudget (w : TransferMatrixWindow) :
    w.pathDepth ≤ transferMatrixBudget w := by
  unfold transferMatrixBudget
  omega

def sampleTransferMatrixWindow : TransferMatrixWindow :=
  { matrixSize := 4, nonzeroEntryWindow := 7, pathDepth := 9, slack := 1 }

example : transferMatrixReady sampleTransferMatrixWindow := by
  norm_num [transferMatrixReady, sampleTransferMatrixWindow]

structure TransferMatrixModelsBudgetCertificate where
  matrixWindow : ℕ
  entryWindow : ℕ
  pathWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransferMatrixModelsBudgetCertificate.controlled
    (c : TransferMatrixModelsBudgetCertificate) : Prop :=
  0 < c.matrixWindow ∧ c.pathWindow ≤ c.matrixWindow + c.entryWindow + c.slack

def TransferMatrixModelsBudgetCertificate.budgetControlled
    (c : TransferMatrixModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.matrixWindow + c.entryWindow + c.pathWindow + c.slack

def TransferMatrixModelsBudgetCertificate.Ready
    (c : TransferMatrixModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TransferMatrixModelsBudgetCertificate.size
    (c : TransferMatrixModelsBudgetCertificate) : ℕ :=
  c.matrixWindow + c.entryWindow + c.pathWindow + c.slack

theorem transferMatrixModels_budgetCertificate_le_size
    (c : TransferMatrixModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleTransferMatrixModelsBudgetCertificate :
    TransferMatrixModelsBudgetCertificate :=
  { matrixWindow := 4
    entryWindow := 7
    pathWindow := 9
    certificateBudgetWindow := 21
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTransferMatrixModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [TransferMatrixModelsBudgetCertificate.controlled,
      sampleTransferMatrixModelsBudgetCertificate]
  · norm_num [TransferMatrixModelsBudgetCertificate.budgetControlled,
      sampleTransferMatrixModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTransferMatrixModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferMatrixModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleTransferMatrixModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [TransferMatrixModelsBudgetCertificate.controlled,
      sampleTransferMatrixModelsBudgetCertificate]
  · norm_num [TransferMatrixModelsBudgetCertificate.budgetControlled,
      sampleTransferMatrixModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List TransferMatrixModelsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleTransferMatrixModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleTransferMatrixModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.TransferMatrixModels
