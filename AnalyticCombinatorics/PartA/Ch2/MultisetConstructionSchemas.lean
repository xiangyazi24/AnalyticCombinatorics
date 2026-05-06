import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multiset construction schemas for labelled classes.

The finite data records atom count, multiplicity budget, and symmetry
budget.
-/

namespace AnalyticCombinatorics.PartA.Ch2.MultisetConstructionSchemas

structure MultisetConstructionData where
  atomCount : ℕ
  multiplicityBudget : ℕ
  symmetryBudget : ℕ
deriving DecidableEq, Repr

def nonemptyMultisetConstruction (d : MultisetConstructionData) : Prop :=
  0 < d.atomCount

def multiplicityControlled (d : MultisetConstructionData) : Prop :=
  d.multiplicityBudget ≤ d.atomCount + d.symmetryBudget

def multisetConstructionReady (d : MultisetConstructionData) : Prop :=
  nonemptyMultisetConstruction d ∧ multiplicityControlled d

def multisetConstructionBudget (d : MultisetConstructionData) : ℕ :=
  d.atomCount + d.multiplicityBudget + d.symmetryBudget

theorem multisetConstructionReady.nonempty {d : MultisetConstructionData}
    (h : multisetConstructionReady d) :
    nonemptyMultisetConstruction d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem atomCount_le_budget (d : MultisetConstructionData) :
    d.atomCount ≤ multisetConstructionBudget d := by
  unfold multisetConstructionBudget
  omega

def sampleMultisetConstruction : MultisetConstructionData :=
  { atomCount := 6, multiplicityBudget := 4, symmetryBudget := 2 }

example : multisetConstructionReady sampleMultisetConstruction := by
  norm_num
    [multisetConstructionReady, nonemptyMultisetConstruction, multiplicityControlled,
      sampleMultisetConstruction]

example : multisetConstructionBudget sampleMultisetConstruction = 12 := by
  native_decide

structure MultisetConstructionBudgetCertificate where
  atomWindow : ℕ
  multiplicityWindow : ℕ
  symmetryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultisetConstructionBudgetCertificate.controlled
    (c : MultisetConstructionBudgetCertificate) : Prop :=
  0 < c.atomWindow ∧
    c.multiplicityWindow ≤ c.atomWindow + c.symmetryWindow + c.slack

def MultisetConstructionBudgetCertificate.budgetControlled
    (c : MultisetConstructionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.atomWindow + c.multiplicityWindow + c.symmetryWindow + c.slack

def MultisetConstructionBudgetCertificate.Ready
    (c : MultisetConstructionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultisetConstructionBudgetCertificate.size
    (c : MultisetConstructionBudgetCertificate) : ℕ :=
  c.atomWindow + c.multiplicityWindow + c.symmetryWindow + c.slack

theorem multisetConstruction_budgetCertificate_le_size
    (c : MultisetConstructionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMultisetConstructionBudgetCertificate :
    MultisetConstructionBudgetCertificate :=
  { atomWindow := 6
    multiplicityWindow := 4
    symmetryWindow := 2
    certificateBudgetWindow := 13
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMultisetConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [MultisetConstructionBudgetCertificate.controlled,
      sampleMultisetConstructionBudgetCertificate]
  · norm_num [MultisetConstructionBudgetCertificate.budgetControlled,
      sampleMultisetConstructionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultisetConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleMultisetConstructionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMultisetConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [MultisetConstructionBudgetCertificate.controlled,
      sampleMultisetConstructionBudgetCertificate]
  · norm_num [MultisetConstructionBudgetCertificate.budgetControlled,
      sampleMultisetConstructionBudgetCertificate]

example :
    sampleMultisetConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleMultisetConstructionBudgetCertificate.size := by
  apply multisetConstruction_budgetCertificate_le_size
  constructor
  · norm_num [MultisetConstructionBudgetCertificate.controlled,
      sampleMultisetConstructionBudgetCertificate]
  · norm_num [MultisetConstructionBudgetCertificate.budgetControlled,
      sampleMultisetConstructionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MultisetConstructionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleMultisetConstructionBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleMultisetConstructionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.MultisetConstructionSchemas
