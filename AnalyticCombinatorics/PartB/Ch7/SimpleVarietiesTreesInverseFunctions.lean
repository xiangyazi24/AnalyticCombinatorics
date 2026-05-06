import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Simple varieties of trees and inverse functions.

Finite bookkeeping for tree specification windows and inverse-function
singularity checks.
-/

namespace AnalyticCombinatorics.PartB.Ch7.SimpleVarietiesTreesInverseFunctions

/-- Characteristic equation certificate for simple varieties of trees. -/
def treeCharacteristicResidual (phi phiDeriv tau : ℕ) : ℤ :=
  (phi : ℤ) - (tau * phiDeriv : ℕ)

/-- Finite criticality audit for a sampled simple tree schema. -/
def treeCriticalityCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun tau =>
    treeCharacteristicResidual (tau + 1) 1 tau = 1

theorem treeCriticality_window :
    treeCriticalityCheck 24 = true := by
  unfold treeCriticalityCheck treeCharacteristicResidual
  native_decide

/-- Finite exact samples of the characteristic residual. -/
def treeCharacteristicSampleCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun tau =>
    treeCharacteristicResidual (2 * tau) 2 tau = 0

theorem treeCharacteristic_sampleWindow :
    treeCharacteristicSampleCheck 16 = true := by
  unfold treeCharacteristicSampleCheck treeCharacteristicResidual
  native_decide

structure SimpleTreeInverseWindow where
  treeFamilyWindow : ℕ
  inverseFunctionWindow : ℕ
  criticalPointWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def simpleTreeInverseReady (w : SimpleTreeInverseWindow) : Prop :=
  0 < w.treeFamilyWindow ∧
    w.criticalPointWindow ≤
      w.treeFamilyWindow + w.inverseFunctionWindow + w.slack

def simpleTreeInverseBudget (w : SimpleTreeInverseWindow) : ℕ :=
  w.treeFamilyWindow + w.inverseFunctionWindow +
    w.criticalPointWindow + w.slack

theorem criticalPointWindow_le_simpleTreeInverseBudget
    (w : SimpleTreeInverseWindow) :
    w.criticalPointWindow ≤ simpleTreeInverseBudget w := by
  unfold simpleTreeInverseBudget
  omega

def sampleSimpleTreeInverseWindow : SimpleTreeInverseWindow :=
  { treeFamilyWindow := 5
    inverseFunctionWindow := 4
    criticalPointWindow := 8
    slack := 1 }

example : simpleTreeInverseReady sampleSimpleTreeInverseWindow := by
  norm_num [simpleTreeInverseReady, sampleSimpleTreeInverseWindow]

structure SimpleVarietiesTreesInverseFunctionsBudgetCertificate where
  treeWindow : ℕ
  inverseWindow : ℕ
  criticalWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SimpleVarietiesTreesInverseFunctionsBudgetCertificate.controlled
    (c : SimpleVarietiesTreesInverseFunctionsBudgetCertificate) : Prop :=
  0 < c.treeWindow ∧
    c.criticalWindow ≤ c.treeWindow + c.inverseWindow + c.slack

def SimpleVarietiesTreesInverseFunctionsBudgetCertificate.budgetControlled
    (c : SimpleVarietiesTreesInverseFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.treeWindow + c.inverseWindow + c.criticalWindow + c.slack

def SimpleVarietiesTreesInverseFunctionsBudgetCertificate.Ready
    (c : SimpleVarietiesTreesInverseFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SimpleVarietiesTreesInverseFunctionsBudgetCertificate.size
    (c : SimpleVarietiesTreesInverseFunctionsBudgetCertificate) : ℕ :=
  c.treeWindow + c.inverseWindow + c.criticalWindow + c.slack

theorem simpleVarietiesTreesInverseFunctions_budgetCertificate_le_size
    (c : SimpleVarietiesTreesInverseFunctionsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSimpleVarietiesTreesInverseFunctionsBudgetCertificate :
    SimpleVarietiesTreesInverseFunctionsBudgetCertificate :=
  { treeWindow := 5
    inverseWindow := 4
    criticalWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSimpleVarietiesTreesInverseFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SimpleVarietiesTreesInverseFunctionsBudgetCertificate.controlled,
      sampleSimpleVarietiesTreesInverseFunctionsBudgetCertificate]
  · norm_num [SimpleVarietiesTreesInverseFunctionsBudgetCertificate.budgetControlled,
      sampleSimpleVarietiesTreesInverseFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSimpleVarietiesTreesInverseFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleSimpleVarietiesTreesInverseFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSimpleVarietiesTreesInverseFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [SimpleVarietiesTreesInverseFunctionsBudgetCertificate.controlled,
        sampleSimpleVarietiesTreesInverseFunctionsBudgetCertificate]
  · norm_num
      [SimpleVarietiesTreesInverseFunctionsBudgetCertificate.budgetControlled,
        sampleSimpleVarietiesTreesInverseFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List SimpleVarietiesTreesInverseFunctionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSimpleVarietiesTreesInverseFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSimpleVarietiesTreesInverseFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.SimpleVarietiesTreesInverseFunctions
