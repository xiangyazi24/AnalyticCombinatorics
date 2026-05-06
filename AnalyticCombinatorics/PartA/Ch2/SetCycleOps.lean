import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
SET and CYC operation schemas.
-/

namespace AnalyticCombinatorics.PartA.Ch2.SetCycleOps

structure SetCycleData where
  setBlocks : ℕ
  cycleBlocks : ℕ
  operationSlack : ℕ
deriving DecidableEq, Repr

def setCycleReady (d : SetCycleData) : Prop :=
  0 < d.setBlocks ∧ d.cycleBlocks ≤ d.setBlocks + d.operationSlack

def setCycleBudget (d : SetCycleData) : ℕ :=
  d.setBlocks + d.cycleBlocks + d.operationSlack

theorem cycleBlocks_le_budget (d : SetCycleData) :
    d.cycleBlocks ≤ setCycleBudget d := by
  unfold setCycleBudget
  omega

def sampleSetCycleData : SetCycleData :=
  { setBlocks := 6, cycleBlocks := 8, operationSlack := 3 }

example : setCycleReady sampleSetCycleData := by
  norm_num [setCycleReady, sampleSetCycleData]

example : setCycleBudget sampleSetCycleData = 17 := by native_decide

structure SetCycleInventory where
  atoms : ℕ
  setComponents : ℕ
  cycleComponents : ℕ
  pointingSlack : ℕ
deriving DecidableEq, Repr

def SetCycleInventory.componentCount (i : SetCycleInventory) : ℕ :=
  i.setComponents + i.cycleComponents

def SetCycleInventory.ready (i : SetCycleInventory) : Prop :=
  i.componentCount ≤ i.atoms + i.pointingSlack

def SetCycleInventory.hasCyclePart (i : SetCycleInventory) : Prop :=
  0 < i.cycleComponents

def SetCycleInventory.certificate (i : SetCycleInventory) : ℕ :=
  i.atoms + i.setComponents + i.cycleComponents + i.pointingSlack

theorem setComponents_le_certificate (i : SetCycleInventory) :
    i.setComponents ≤ i.certificate := by
  unfold SetCycleInventory.certificate
  omega

def sampleSetCycleInventory : SetCycleInventory :=
  { atoms := 9, setComponents := 4, cycleComponents := 3, pointingSlack := 0 }

example : sampleSetCycleInventory.ready := by
  norm_num [sampleSetCycleInventory, SetCycleInventory.ready, SetCycleInventory.componentCount]

example : sampleSetCycleInventory.hasCyclePart := by
  norm_num [sampleSetCycleInventory, SetCycleInventory.hasCyclePart]


structure SetCycleOpsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SetCycleOpsBudgetCertificate.controlled
    (c : SetCycleOpsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SetCycleOpsBudgetCertificate.budgetControlled
    (c : SetCycleOpsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SetCycleOpsBudgetCertificate.Ready
    (c : SetCycleOpsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SetCycleOpsBudgetCertificate.size
    (c : SetCycleOpsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem setCycleOps_budgetCertificate_le_size
    (c : SetCycleOpsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSetCycleOpsBudgetCertificate :
    SetCycleOpsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSetCycleOpsBudgetCertificate.Ready := by
  constructor
  · norm_num [SetCycleOpsBudgetCertificate.controlled,
      sampleSetCycleOpsBudgetCertificate]
  · norm_num [SetCycleOpsBudgetCertificate.budgetControlled,
      sampleSetCycleOpsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSetCycleOpsBudgetCertificate.certificateBudgetWindow ≤
      sampleSetCycleOpsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSetCycleOpsBudgetCertificate.Ready := by
  constructor
  · norm_num [SetCycleOpsBudgetCertificate.controlled,
      sampleSetCycleOpsBudgetCertificate]
  · norm_num [SetCycleOpsBudgetCertificate.budgetControlled,
      sampleSetCycleOpsBudgetCertificate]

example :
    sampleSetCycleOpsBudgetCertificate.certificateBudgetWindow ≤
      sampleSetCycleOpsBudgetCertificate.size := by
  apply setCycleOps_budgetCertificate_le_size
  constructor
  · norm_num [SetCycleOpsBudgetCertificate.controlled,
      sampleSetCycleOpsBudgetCertificate]
  · norm_num [SetCycleOpsBudgetCertificate.budgetControlled,
      sampleSetCycleOpsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SetCycleOpsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSetCycleOpsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSetCycleOpsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.SetCycleOps
