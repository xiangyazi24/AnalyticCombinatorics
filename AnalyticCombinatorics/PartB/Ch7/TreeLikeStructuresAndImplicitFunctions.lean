import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Tree-like structures and implicit functions
-/

namespace AnalyticCombinatorics.PartB.Ch7.TreeLikeStructuresAndImplicitFunctions

/-- Finite implicit-function schema data for tree-like classes. -/
structure ImplicitTreeSchema where
  equationCount : ℕ
  dependencyCount : ℕ
  transferScale : ℕ
deriving DecidableEq, Repr

def ImplicitTreeSchema.ready (s : ImplicitTreeSchema) : Prop :=
  0 < s.equationCount ∧ s.dependencyCount ≤ s.transferScale + s.equationCount

theorem implicitTreeSchema_sample_ready :
    ({ equationCount := 1, dependencyCount := 4,
       transferScale := 3 } : ImplicitTreeSchema).ready := by
  norm_num [ImplicitTreeSchema.ready]

/-- Cleared square-root transfer certificate for implicit tree schemas. -/
def implicitTreeTransferProxy (scale n : ℕ) : ℕ :=
  scale * (n + 1)

theorem implicitTreeTransferProxy_sample :
    implicitTreeTransferProxy 3 4 = 15 := by
  native_decide

structure ImplicitTreeWindow where
  treeWindow : ℕ
  implicitWindow : ℕ
  transferWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitTreeWindow.ready (w : ImplicitTreeWindow) : Prop :=
  0 < w.treeWindow ∧
    w.implicitWindow ≤ w.treeWindow + w.transferWindow + w.slack

def sampleImplicitTreeWindow : ImplicitTreeWindow :=
  { treeWindow := 4, implicitWindow := 7, transferWindow := 3, slack := 0 }

example : sampleImplicitTreeWindow.ready := by
  norm_num [ImplicitTreeWindow.ready, sampleImplicitTreeWindow]

structure BudgetCertificate where
  treeWindow : ℕ
  implicitWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.treeWindow ∧ c.implicitWindow ≤ c.treeWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.treeWindow + c.implicitWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.treeWindow + c.implicitWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { treeWindow := 5, implicitWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  have h : sampleBudgetCertificate.Ready := by
    constructor
    · norm_num [BudgetCertificate.controlled,
        sampleBudgetCertificate]
    · norm_num [BudgetCertificate.budgetControlled,
        sampleBudgetCertificate]
  exact h.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.TreeLikeStructuresAndImplicitFunctions
