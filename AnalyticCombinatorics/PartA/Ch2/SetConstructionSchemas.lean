import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Set construction schemas for labelled classes.

The module records finite block counts and atom budgets for SET-like
constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch2.SetConstructionSchemas

structure SetConstructionData where
  atomCount : ℕ
  blockCount : ℕ
  symmetryBudget : ℕ
deriving DecidableEq, Repr

def nonemptySetConstruction (d : SetConstructionData) : Prop :=
  0 < d.atomCount

def blockBudgetControlled (d : SetConstructionData) : Prop :=
  d.blockCount ≤ d.atomCount + d.symmetryBudget

def setConstructionReady (d : SetConstructionData) : Prop :=
  nonemptySetConstruction d ∧ blockBudgetControlled d

def totalSetBudget (d : SetConstructionData) : ℕ :=
  d.atomCount + d.blockCount + d.symmetryBudget

theorem setConstructionReady.nonempty {d : SetConstructionData}
    (h : setConstructionReady d) :
    nonemptySetConstruction d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem atomCount_le_total (d : SetConstructionData) :
    d.atomCount ≤ totalSetBudget d := by
  unfold totalSetBudget
  omega

def sampleSetConstruction : SetConstructionData :=
  { atomCount := 5, blockCount := 3, symmetryBudget := 2 }

example : setConstructionReady sampleSetConstruction := by
  norm_num
    [setConstructionReady, nonemptySetConstruction, blockBudgetControlled,
      sampleSetConstruction]

example : totalSetBudget sampleSetConstruction = 10 := by
  native_decide

structure SetConstructionBudgetCertificate where
  atomWindow : ℕ
  blockWindow : ℕ
  symmetryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SetConstructionBudgetCertificate.controlled
    (c : SetConstructionBudgetCertificate) : Prop :=
  0 < c.atomWindow ∧
    c.blockWindow ≤ c.atomWindow + c.symmetryWindow + c.slack

def SetConstructionBudgetCertificate.budgetControlled
    (c : SetConstructionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.atomWindow + c.blockWindow + c.symmetryWindow + c.slack

def SetConstructionBudgetCertificate.Ready
    (c : SetConstructionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SetConstructionBudgetCertificate.size
    (c : SetConstructionBudgetCertificate) : ℕ :=
  c.atomWindow + c.blockWindow + c.symmetryWindow + c.slack

theorem setConstruction_budgetCertificate_le_size
    (c : SetConstructionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSetConstructionBudgetCertificate :
    SetConstructionBudgetCertificate :=
  { atomWindow := 5
    blockWindow := 3
    symmetryWindow := 2
    certificateBudgetWindow := 11
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSetConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [SetConstructionBudgetCertificate.controlled,
      sampleSetConstructionBudgetCertificate]
  · norm_num [SetConstructionBudgetCertificate.budgetControlled,
      sampleSetConstructionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSetConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleSetConstructionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSetConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [SetConstructionBudgetCertificate.controlled,
      sampleSetConstructionBudgetCertificate]
  · norm_num [SetConstructionBudgetCertificate.budgetControlled,
      sampleSetConstructionBudgetCertificate]

example :
    sampleSetConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleSetConstructionBudgetCertificate.size := by
  apply setConstruction_budgetCertificate_le_size
  constructor
  · norm_num [SetConstructionBudgetCertificate.controlled,
      sampleSetConstructionBudgetCertificate]
  · norm_num [SetConstructionBudgetCertificate.budgetControlled,
      sampleSetConstructionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SetConstructionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSetConstructionBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSetConstructionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.SetConstructionSchemas
