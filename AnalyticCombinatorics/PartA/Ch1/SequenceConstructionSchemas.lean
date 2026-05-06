import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Sequence construction schemas.

The file records finite sequence-length and atom-budget calculations for
SEQ constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.SequenceConstructionSchemas

structure SequenceConstructionData where
  lengthBudget : ℕ
  atomBudget : ℕ
  guardBudget : ℕ
deriving DecidableEq, Repr

def nonemptySequenceBudget (d : SequenceConstructionData) : Prop :=
  0 < d.lengthBudget

def sequenceAtomsControlled (d : SequenceConstructionData) : Prop :=
  d.atomBudget ≤ d.lengthBudget + d.guardBudget

def sequenceConstructionReady (d : SequenceConstructionData) : Prop :=
  nonemptySequenceBudget d ∧ sequenceAtomsControlled d

def sequenceConstructionBudget (d : SequenceConstructionData) : ℕ :=
  d.lengthBudget + d.atomBudget + d.guardBudget

theorem sequenceConstructionReady.nonempty {d : SequenceConstructionData}
    (h : sequenceConstructionReady d) :
    nonemptySequenceBudget d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem lengthBudget_le_total (d : SequenceConstructionData) :
    d.lengthBudget ≤ sequenceConstructionBudget d := by
  unfold sequenceConstructionBudget
  omega

def sampleSequenceConstruction : SequenceConstructionData :=
  { lengthBudget := 5, atomBudget := 7, guardBudget := 3 }

example : sequenceConstructionReady sampleSequenceConstruction := by
  norm_num
    [sequenceConstructionReady, nonemptySequenceBudget, sequenceAtomsControlled,
      sampleSequenceConstruction]

example : sequenceConstructionBudget sampleSequenceConstruction = 15 := by
  native_decide

structure SequenceConstructionBudgetCertificate where
  lengthWindow : ℕ
  atomWindow : ℕ
  guardWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SequenceConstructionBudgetCertificate.controlled
    (c : SequenceConstructionBudgetCertificate) : Prop :=
  0 < c.lengthWindow ∧
    c.atomWindow ≤ c.lengthWindow + c.guardWindow + c.slack

def SequenceConstructionBudgetCertificate.budgetControlled
    (c : SequenceConstructionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.lengthWindow + c.atomWindow + c.guardWindow + c.slack

def SequenceConstructionBudgetCertificate.Ready
    (c : SequenceConstructionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SequenceConstructionBudgetCertificate.size
    (c : SequenceConstructionBudgetCertificate) : ℕ :=
  c.lengthWindow + c.atomWindow + c.guardWindow + c.slack

theorem sequenceConstruction_budgetCertificate_le_size
    (c : SequenceConstructionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSequenceConstructionBudgetCertificate :
    SequenceConstructionBudgetCertificate :=
  { lengthWindow := 5
    atomWindow := 7
    guardWindow := 3
    certificateBudgetWindow := 16
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSequenceConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [SequenceConstructionBudgetCertificate.controlled,
      sampleSequenceConstructionBudgetCertificate]
  · norm_num [SequenceConstructionBudgetCertificate.budgetControlled,
      sampleSequenceConstructionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSequenceConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleSequenceConstructionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSequenceConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [SequenceConstructionBudgetCertificate.controlled,
      sampleSequenceConstructionBudgetCertificate]
  · norm_num [SequenceConstructionBudgetCertificate.budgetControlled,
      sampleSequenceConstructionBudgetCertificate]

example :
    sampleSequenceConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleSequenceConstructionBudgetCertificate.size := by
  apply sequenceConstruction_budgetCertificate_le_size
  constructor
  · norm_num [SequenceConstructionBudgetCertificate.controlled,
      sampleSequenceConstructionBudgetCertificate]
  · norm_num [SequenceConstructionBudgetCertificate.budgetControlled,
      sampleSequenceConstructionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SequenceConstructionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSequenceConstructionBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSequenceConstructionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.SequenceConstructionSchemas
