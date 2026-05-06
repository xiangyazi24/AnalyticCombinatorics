import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite cycle index models.

The finite record stores orbit count, cycle count, and symmetry slack for
cycle-index bookkeeping.
-/

namespace AnalyticCombinatorics.AppA.FiniteCycleIndexModels

structure CycleIndexData where
  orbitCount : ℕ
  cycleCount : ℕ
  symmetrySlack : ℕ
deriving DecidableEq, Repr

def orbitsNonempty (d : CycleIndexData) : Prop :=
  0 < d.orbitCount

def cyclesControlled (d : CycleIndexData) : Prop :=
  d.cycleCount ≤ d.orbitCount + d.symmetrySlack

def cycleIndexReady (d : CycleIndexData) : Prop :=
  orbitsNonempty d ∧ cyclesControlled d

def cycleIndexBudget (d : CycleIndexData) : ℕ :=
  d.orbitCount + d.cycleCount + d.symmetrySlack

theorem cycleIndexReady.orbits {d : CycleIndexData}
    (h : cycleIndexReady d) :
    orbitsNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem cycleCount_le_cycleIndexBudget (d : CycleIndexData) :
    d.cycleCount ≤ cycleIndexBudget d := by
  unfold cycleIndexBudget
  omega

def sampleCycleIndexData : CycleIndexData :=
  { orbitCount := 5, cycleCount := 7, symmetrySlack := 3 }

example : cycleIndexReady sampleCycleIndexData := by
  norm_num [cycleIndexReady, orbitsNonempty]
  norm_num [cyclesControlled, sampleCycleIndexData]

example : cycleIndexBudget sampleCycleIndexData = 15 := by
  native_decide

structure CycleIndexWindow where
  orbitCount : ℕ
  cycleCount : ℕ
  symmetrySlack : ℕ
  monomialBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CycleIndexWindow.cyclesControlled (w : CycleIndexWindow) : Prop :=
  w.cycleCount ≤ w.orbitCount + w.symmetrySlack + w.slack

def CycleIndexWindow.monomialControlled (w : CycleIndexWindow) : Prop :=
  w.monomialBudget ≤ w.orbitCount + w.cycleCount + w.symmetrySlack + w.slack

def cycleIndexWindowReady (w : CycleIndexWindow) : Prop :=
  0 < w.orbitCount ∧
    w.cyclesControlled ∧
    w.monomialControlled

def CycleIndexWindow.certificate (w : CycleIndexWindow) : ℕ :=
  w.orbitCount + w.cycleCount + w.symmetrySlack + w.slack

theorem cycleIndex_monomialBudget_le_certificate {w : CycleIndexWindow}
    (h : cycleIndexWindowReady w) :
    w.monomialBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hmono⟩
  exact hmono

def sampleCycleIndexWindow : CycleIndexWindow :=
  { orbitCount := 5, cycleCount := 7, symmetrySlack := 3, monomialBudget := 12, slack := 0 }

example : cycleIndexWindowReady sampleCycleIndexWindow := by
  norm_num [cycleIndexWindowReady, CycleIndexWindow.cyclesControlled,
    CycleIndexWindow.monomialControlled, sampleCycleIndexWindow]

example : sampleCycleIndexWindow.certificate = 15 := by
  native_decide


structure FiniteCycleIndexModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteCycleIndexModelsBudgetCertificate.controlled
    (c : FiniteCycleIndexModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteCycleIndexModelsBudgetCertificate.budgetControlled
    (c : FiniteCycleIndexModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteCycleIndexModelsBudgetCertificate.Ready
    (c : FiniteCycleIndexModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteCycleIndexModelsBudgetCertificate.size
    (c : FiniteCycleIndexModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCycleIndexModels_budgetCertificate_le_size
    (c : FiniteCycleIndexModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteCycleIndexModelsBudgetCertificate :
    FiniteCycleIndexModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteCycleIndexModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCycleIndexModelsBudgetCertificate.controlled,
      sampleFiniteCycleIndexModelsBudgetCertificate]
  · norm_num [FiniteCycleIndexModelsBudgetCertificate.budgetControlled,
      sampleFiniteCycleIndexModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteCycleIndexModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCycleIndexModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteCycleIndexModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCycleIndexModelsBudgetCertificate.controlled,
      sampleFiniteCycleIndexModelsBudgetCertificate]
  · norm_num [FiniteCycleIndexModelsBudgetCertificate.budgetControlled,
      sampleFiniteCycleIndexModelsBudgetCertificate]

example :
    sampleFiniteCycleIndexModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCycleIndexModelsBudgetCertificate.size := by
  apply finiteCycleIndexModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteCycleIndexModelsBudgetCertificate.controlled,
      sampleFiniteCycleIndexModelsBudgetCertificate]
  · norm_num [FiniteCycleIndexModelsBudgetCertificate.budgetControlled,
      sampleFiniteCycleIndexModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteCycleIndexModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteCycleIndexModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteCycleIndexModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteCycleIndexModels
