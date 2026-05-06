import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
General tree schemas.

The main finite count table records the Catalan specialization, while
`taryTreeCount` records the Fuss-Catalan closed form for full `t`-ary trees.
-/

namespace AnalyticCombinatorics.PartA.Ch1.GeneralTrees

structure GeneralTreeWindow where
  nodeCount : ℕ
  childSlots : ℕ
  recursionSlack : ℕ
deriving DecidableEq, Repr

def nonemptyTreeWindow (w : GeneralTreeWindow) : Prop :=
  0 < w.nodeCount

def childSlotsControlled (w : GeneralTreeWindow) : Prop :=
  w.childSlots ≤ w.nodeCount + w.recursionSlack

def generalTreeWindowReady (w : GeneralTreeWindow) : Prop :=
  nonemptyTreeWindow w ∧ childSlotsControlled w

def generalTreeWindowBudget (w : GeneralTreeWindow) : ℕ :=
  w.nodeCount + w.childSlots + w.recursionSlack

theorem generalTreeWindowReady.certificate {w : GeneralTreeWindow}
    (h : generalTreeWindowReady w) :
    nonemptyTreeWindow w ∧ childSlotsControlled w ∧
      w.childSlots ≤ generalTreeWindowBudget w := by
  rcases h with ⟨hnodes, hcontrolled⟩
  refine ⟨hnodes, hcontrolled, ?_⟩
  unfold generalTreeWindowBudget
  omega

theorem nodeCount_le_budget (w : GeneralTreeWindow) :
    w.nodeCount ≤ generalTreeWindowBudget w := by
  unfold generalTreeWindowBudget
  omega

def taryTreeCount (arity internalNodes : ℕ) : ℕ :=
  Nat.choose (arity * internalNodes + 1) internalNodes / (arity * internalNodes + 1)

def fussCatalanNumerator (arity internalNodes : ℕ) : ℕ :=
  Nat.choose (arity * internalNodes + 1) internalNodes

def fussCatalanDenominator (arity internalNodes : ℕ) : ℕ :=
  arity * internalNodes + 1

def binaryTreeCount (n : ℕ) : ℕ :=
  taryTreeCount 2 n

def generalTreeCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 42
  | _ => 0

def fullTreeBudget (arity internalNodes slack : ℕ) : ℕ :=
  arity * internalNodes + slack

def sampleGeneralTreeWindow : GeneralTreeWindow :=
  { nodeCount := 5, childSlots := 7, recursionSlack := 2 }

example : generalTreeWindowReady sampleGeneralTreeWindow := by
  norm_num [generalTreeWindowReady, nonemptyTreeWindow]
  norm_num [childSlotsControlled, sampleGeneralTreeWindow]

example : generalTreeCount 5 = 42 := by native_decide
example : generalTreeWindowBudget sampleGeneralTreeWindow = 14 := by native_decide
example : taryTreeCount 2 4 = 14 := by native_decide
example : taryTreeCount 3 4 = 55 := by native_decide
example : fussCatalanNumerator 3 4 = 715 := by native_decide
example : fussCatalanDenominator 3 4 = 13 := by native_decide
example : binaryTreeCount 5 = generalTreeCount 5 := by native_decide
example : fullTreeBudget 3 5 2 = 17 := by native_decide


structure GeneralTreesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GeneralTreesBudgetCertificate.controlled
    (c : GeneralTreesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def GeneralTreesBudgetCertificate.budgetControlled
    (c : GeneralTreesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def GeneralTreesBudgetCertificate.Ready
    (c : GeneralTreesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GeneralTreesBudgetCertificate.size
    (c : GeneralTreesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem generalTrees_budgetCertificate_le_size
    (c : GeneralTreesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGeneralTreesBudgetCertificate :
    GeneralTreesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleGeneralTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [GeneralTreesBudgetCertificate.controlled,
      sampleGeneralTreesBudgetCertificate]
  · norm_num [GeneralTreesBudgetCertificate.budgetControlled,
      sampleGeneralTreesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGeneralTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleGeneralTreesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleGeneralTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [GeneralTreesBudgetCertificate.controlled,
      sampleGeneralTreesBudgetCertificate]
  · norm_num [GeneralTreesBudgetCertificate.budgetControlled,
      sampleGeneralTreesBudgetCertificate]

example :
    sampleGeneralTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleGeneralTreesBudgetCertificate.size := by
  apply generalTrees_budgetCertificate_le_size
  constructor
  · norm_num [GeneralTreesBudgetCertificate.controlled,
      sampleGeneralTreesBudgetCertificate]
  · norm_num [GeneralTreesBudgetCertificate.budgetControlled,
      sampleGeneralTreesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List GeneralTreesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGeneralTreesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleGeneralTreesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.GeneralTrees
