import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Digital-search-tree limit schema bookkeeping.

The finite data records alphabet size, toll growth, and variance budgets for
digital search tree limit laws.
-/

namespace AnalyticCombinatorics.PartB.Ch9.DigitalSearchTreeLimitSchemas

structure DSTData where
  alphabetSize : ℕ
  tollBudget : ℕ
  varianceBudget : ℕ
deriving DecidableEq, Repr

def positiveAlphabet (d : DSTData) : Prop :=
  1 < d.alphabetSize

def varianceNonzero (d : DSTData) : Prop :=
  0 < d.varianceBudget

def dstLimitReady (d : DSTData) : Prop :=
  positiveAlphabet d ∧ varianceNonzero d

def branchingBudget (d : DSTData) (depth : ℕ) : ℕ :=
  d.alphabetSize ^ depth + d.tollBudget

theorem dstLimitReady.alphabet {d : DSTData}
    (h : dstLimitReady d) :
    positiveAlphabet d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem branchingBudget_ge_toll (d : DSTData) (depth : ℕ) :
    d.tollBudget ≤ branchingBudget d depth := by
  unfold branchingBudget
  omega

def sampleDST : DSTData :=
  { alphabetSize := 2, tollBudget := 5, varianceBudget := 7 }

example : dstLimitReady sampleDST := by
  norm_num [dstLimitReady, positiveAlphabet, varianceNonzero, sampleDST]

example : branchingBudget sampleDST 4 = 21 := by
  native_decide

/-- Finite executable readiness audit for digital-search-tree limit data. -/
def dstLimitDataListReady (data : List DSTData) : Bool :=
  data.all fun d =>
    1 < d.alphabetSize && 0 < d.varianceBudget

theorem dstLimitDataList_readyWindow :
    dstLimitDataListReady
      [{ alphabetSize := 2, tollBudget := 3, varianceBudget := 4 },
       { alphabetSize := 2, tollBudget := 5, varianceBudget := 7 }] = true := by
  unfold dstLimitDataListReady
  native_decide

structure DSTLimitWindow where
  alphabetSize : ℕ
  depth : ℕ
  tollBudget : ℕ
  varianceBudget : ℕ
  nodeBudget : ℕ
deriving DecidableEq, Repr

def DSTLimitWindow.tollControlled (w : DSTLimitWindow) : Prop :=
  w.tollBudget ≤ w.nodeBudget + w.varianceBudget

def DSTLimitWindow.nodeControlled (w : DSTLimitWindow) : Prop :=
  w.nodeBudget ≤ w.alphabetSize ^ (w.depth + 1) + w.tollBudget

def dstLimitWindowReady (w : DSTLimitWindow) : Prop :=
  1 < w.alphabetSize ∧
    0 < w.varianceBudget ∧
    w.tollControlled ∧
    w.nodeControlled

def DSTLimitWindow.certificate (w : DSTLimitWindow) : ℕ :=
  w.alphabetSize ^ (w.depth + 1) + w.tollBudget

theorem dst_nodeBudget_le_certificate {w : DSTLimitWindow}
    (h : dstLimitWindowReady w) :
    w.nodeBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hnode⟩
  exact hnode

def sampleDSTLimitWindow : DSTLimitWindow :=
  { alphabetSize := 2, depth := 4, tollBudget := 5, varianceBudget := 7, nodeBudget := 16 }

example : dstLimitWindowReady sampleDSTLimitWindow := by
  norm_num [dstLimitWindowReady, DSTLimitWindow.tollControlled,
    DSTLimitWindow.nodeControlled, sampleDSTLimitWindow]

example : sampleDSTLimitWindow.certificate = 37 := by
  native_decide


structure DigitalSearchTreeLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DigitalSearchTreeLimitSchemasBudgetCertificate.controlled
    (c : DigitalSearchTreeLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DigitalSearchTreeLimitSchemasBudgetCertificate.budgetControlled
    (c : DigitalSearchTreeLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DigitalSearchTreeLimitSchemasBudgetCertificate.Ready
    (c : DigitalSearchTreeLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DigitalSearchTreeLimitSchemasBudgetCertificate.size
    (c : DigitalSearchTreeLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem digitalSearchTreeLimitSchemas_budgetCertificate_le_size
    (c : DigitalSearchTreeLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDigitalSearchTreeLimitSchemasBudgetCertificate :
    DigitalSearchTreeLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleDigitalSearchTreeLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DigitalSearchTreeLimitSchemasBudgetCertificate.controlled,
      sampleDigitalSearchTreeLimitSchemasBudgetCertificate]
  · norm_num [DigitalSearchTreeLimitSchemasBudgetCertificate.budgetControlled,
      sampleDigitalSearchTreeLimitSchemasBudgetCertificate]

example :
    sampleDigitalSearchTreeLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDigitalSearchTreeLimitSchemasBudgetCertificate.size := by
  apply digitalSearchTreeLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DigitalSearchTreeLimitSchemasBudgetCertificate.controlled,
      sampleDigitalSearchTreeLimitSchemasBudgetCertificate]
  · norm_num [DigitalSearchTreeLimitSchemasBudgetCertificate.budgetControlled,
      sampleDigitalSearchTreeLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDigitalSearchTreeLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DigitalSearchTreeLimitSchemasBudgetCertificate.controlled,
      sampleDigitalSearchTreeLimitSchemasBudgetCertificate]
  · norm_num [DigitalSearchTreeLimitSchemasBudgetCertificate.budgetControlled,
      sampleDigitalSearchTreeLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDigitalSearchTreeLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDigitalSearchTreeLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List DigitalSearchTreeLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDigitalSearchTreeLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleDigitalSearchTreeLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.DigitalSearchTreeLimitSchemas
