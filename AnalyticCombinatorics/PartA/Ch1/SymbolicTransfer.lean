import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Symbolic transfer schemas.
-/

namespace AnalyticCombinatorics.PartA.Ch1.SymbolicTransfer

structure TransferData where
  constructorCount : ℕ
  coefficientWindow : ℕ
  transferSlack : ℕ
deriving DecidableEq, Repr

def transferReady (d : TransferData) : Prop :=
  0 < d.constructorCount ∧
    d.coefficientWindow ≤ d.constructorCount + d.transferSlack

def transferBudget (d : TransferData) : ℕ :=
  d.constructorCount + d.coefficientWindow + d.transferSlack

theorem coefficientWindow_le_budget (d : TransferData) :
    d.coefficientWindow ≤ transferBudget d := by
  unfold transferBudget
  omega

def sampleTransferData : TransferData :=
  { constructorCount := 6, coefficientWindow := 8, transferSlack := 3 }

example : transferReady sampleTransferData := by
  norm_num [transferReady, sampleTransferData]

inductive ConstructorKind where
  | atom
  | sum
  | product
  | sequence
  | set
  | cycle
deriving DecidableEq, Repr

def constructorArity : ConstructorKind → ℕ
  | .atom => 0
  | .sum => 2
  | .product => 2
  | .sequence => 1
  | .set => 1
  | .cycle => 1

def constructorWeight : ConstructorKind → ℕ
  | .atom => 1
  | .sum => 2
  | .product => 3
  | .sequence => 4
  | .set => 5
  | .cycle => 6

structure SymbolicRuleWindow where
  root : ConstructorKind
  auxiliaryConstructors : ℕ
  coefficientDepth : ℕ
  closureSlack : ℕ
deriving DecidableEq, Repr

def SymbolicRuleWindow.arityBudget (w : SymbolicRuleWindow) : ℕ :=
  constructorArity w.root + w.auxiliaryConstructors + w.closureSlack

def SymbolicRuleWindow.weightBudget (w : SymbolicRuleWindow) : ℕ :=
  constructorWeight w.root + w.coefficientDepth + w.closureSlack

def SymbolicRuleWindow.ready (w : SymbolicRuleWindow) : Prop :=
  w.coefficientDepth ≤ w.arityBudget + w.weightBudget

def SymbolicRuleWindow.certificate (w : SymbolicRuleWindow) : ℕ :=
  w.arityBudget + w.weightBudget + w.auxiliaryConstructors

theorem auxiliaryConstructors_le_certificate (w : SymbolicRuleWindow) :
    w.auxiliaryConstructors ≤ w.certificate := by
  unfold SymbolicRuleWindow.certificate
  omega

def sampleSymbolicRuleWindow : SymbolicRuleWindow :=
  { root := ConstructorKind.sequence,
    auxiliaryConstructors := 3,
    coefficientDepth := 8,
    closureSlack := 1 }

example : sampleSymbolicRuleWindow.ready := by
  norm_num [sampleSymbolicRuleWindow, SymbolicRuleWindow.ready, SymbolicRuleWindow.arityBudget,
    SymbolicRuleWindow.weightBudget, constructorArity, constructorWeight]

example : sampleSymbolicRuleWindow.certificate = 21 := by
  norm_num [sampleSymbolicRuleWindow, SymbolicRuleWindow.certificate,
    SymbolicRuleWindow.arityBudget, SymbolicRuleWindow.weightBudget, constructorArity,
    constructorWeight]


structure SymbolicTransferBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SymbolicTransferBudgetCertificate.controlled
    (c : SymbolicTransferBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SymbolicTransferBudgetCertificate.budgetControlled
    (c : SymbolicTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SymbolicTransferBudgetCertificate.Ready
    (c : SymbolicTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SymbolicTransferBudgetCertificate.size
    (c : SymbolicTransferBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem symbolicTransfer_budgetCertificate_le_size
    (c : SymbolicTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSymbolicTransferBudgetCertificate :
    SymbolicTransferBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSymbolicTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [SymbolicTransferBudgetCertificate.controlled,
      sampleSymbolicTransferBudgetCertificate]
  · norm_num [SymbolicTransferBudgetCertificate.budgetControlled,
      sampleSymbolicTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSymbolicTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleSymbolicTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSymbolicTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [SymbolicTransferBudgetCertificate.controlled,
      sampleSymbolicTransferBudgetCertificate]
  · norm_num [SymbolicTransferBudgetCertificate.budgetControlled,
      sampleSymbolicTransferBudgetCertificate]

example :
    sampleSymbolicTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleSymbolicTransferBudgetCertificate.size := by
  apply symbolicTransfer_budgetCertificate_le_size
  constructor
  · norm_num [SymbolicTransferBudgetCertificate.controlled,
      sampleSymbolicTransferBudgetCertificate]
  · norm_num [SymbolicTransferBudgetCertificate.budgetControlled,
      sampleSymbolicTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SymbolicTransferBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSymbolicTransferBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSymbolicTransferBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.SymbolicTransfer
