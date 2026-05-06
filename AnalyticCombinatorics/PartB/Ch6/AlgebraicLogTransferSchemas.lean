import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Algebraic-log transfer schemas.

The finite record stores algebraic order, logarithmic order, and transfer
slack.
-/

namespace AnalyticCombinatorics.PartB.Ch6.AlgebraicLogTransferSchemas

structure AlgebraicLogTransferData where
  algebraicOrder : ℕ
  logarithmicOrder : ℕ
  transferSlack : ℕ
deriving DecidableEq, Repr

def algebraicOrderPositive (d : AlgebraicLogTransferData) : Prop :=
  0 < d.algebraicOrder

def logarithmicOrderControlled (d : AlgebraicLogTransferData) : Prop :=
  d.logarithmicOrder ≤ d.algebraicOrder + d.transferSlack

def algebraicLogTransferReady (d : AlgebraicLogTransferData) : Prop :=
  algebraicOrderPositive d ∧ logarithmicOrderControlled d

def algebraicLogTransferBudget (d : AlgebraicLogTransferData) : ℕ :=
  d.algebraicOrder + d.logarithmicOrder + d.transferSlack

theorem algebraicLogTransferReady.algebraic
    {d : AlgebraicLogTransferData}
    (h : algebraicLogTransferReady d) :
    algebraicOrderPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem logarithmicOrder_le_algebraicLogBudget
    (d : AlgebraicLogTransferData) :
    d.logarithmicOrder ≤ algebraicLogTransferBudget d := by
  unfold algebraicLogTransferBudget
  omega

def sampleAlgebraicLogTransferData : AlgebraicLogTransferData :=
  { algebraicOrder := 4, logarithmicOrder := 6, transferSlack := 3 }

example : algebraicLogTransferReady sampleAlgebraicLogTransferData := by
  norm_num [algebraicLogTransferReady, algebraicOrderPositive]
  norm_num [logarithmicOrderControlled, sampleAlgebraicLogTransferData]

example : algebraicLogTransferBudget sampleAlgebraicLogTransferData = 13 := by
  native_decide

structure AlgebraicLogTransferBudgetCertificate where
  algebraicOrderWindow : ℕ
  logarithmicOrderWindow : ℕ
  transferSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlgebraicLogTransferBudgetCertificate.controlled
    (c : AlgebraicLogTransferBudgetCertificate) : Prop :=
  0 < c.algebraicOrderWindow ∧
    c.logarithmicOrderWindow ≤
      c.algebraicOrderWindow + c.transferSlackWindow + c.slack

def AlgebraicLogTransferBudgetCertificate.budgetControlled
    (c : AlgebraicLogTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.algebraicOrderWindow + c.logarithmicOrderWindow + c.transferSlackWindow +
      c.slack

def AlgebraicLogTransferBudgetCertificate.Ready
    (c : AlgebraicLogTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlgebraicLogTransferBudgetCertificate.size
    (c : AlgebraicLogTransferBudgetCertificate) : ℕ :=
  c.algebraicOrderWindow + c.logarithmicOrderWindow + c.transferSlackWindow +
    c.slack

theorem algebraicLogTransfer_budgetCertificate_le_size
    (c : AlgebraicLogTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAlgebraicLogTransferBudgetCertificate :
    AlgebraicLogTransferBudgetCertificate :=
  { algebraicOrderWindow := 4
    logarithmicOrderWindow := 6
    transferSlackWindow := 3
    certificateBudgetWindow := 14
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAlgebraicLogTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicLogTransferBudgetCertificate.controlled,
      sampleAlgebraicLogTransferBudgetCertificate]
  · norm_num [AlgebraicLogTransferBudgetCertificate.budgetControlled,
      sampleAlgebraicLogTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlgebraicLogTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicLogTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAlgebraicLogTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicLogTransferBudgetCertificate.controlled,
      sampleAlgebraicLogTransferBudgetCertificate]
  · norm_num [AlgebraicLogTransferBudgetCertificate.budgetControlled,
      sampleAlgebraicLogTransferBudgetCertificate]

example :
    sampleAlgebraicLogTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicLogTransferBudgetCertificate.size := by
  apply algebraicLogTransfer_budgetCertificate_le_size
  constructor
  · norm_num [AlgebraicLogTransferBudgetCertificate.controlled,
      sampleAlgebraicLogTransferBudgetCertificate]
  · norm_num [AlgebraicLogTransferBudgetCertificate.budgetControlled,
      sampleAlgebraicLogTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AlgebraicLogTransferBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAlgebraicLogTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAlgebraicLogTransferBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.AlgebraicLogTransferSchemas
