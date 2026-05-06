import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Tree-like structures and implicit functions.

Finite bookkeeping for implicit tree schemas and their singular windows.
-/

namespace AnalyticCombinatorics.PartB.Ch7.TreeLikeStructuresImplicitFunctions

/-- Tree schema residual `T = z * (1 + T)^2` over integer samples. -/
def treeSchemaResidual (z t : ℤ) : ℤ :=
  t - z * (1 + t) ^ 2

/-- Derivative in the tree variable. -/
def treeSchemaDerivativeT (z t : ℤ) : ℤ :=
  1 - z * (2 * (1 + t))

/-- Finite noncriticality check near the ordinary point. -/
def treeSchemaNoncriticalAtOrigin : Prop :=
  treeSchemaResidual 0 0 = 0 ∧ treeSchemaDerivativeT 0 0 = 1

theorem treeSchema_originNoncritical :
    treeSchemaNoncriticalAtOrigin := by
  norm_num [treeSchemaNoncriticalAtOrigin, treeSchemaResidual,
    treeSchemaDerivativeT]

def TreeSchemaSampleWindow (z t residual derivative : ℤ) : Prop :=
  treeSchemaResidual z t = residual ∧ treeSchemaDerivativeT z t = derivative

theorem treeSchema_sampleWindow :
    TreeSchemaSampleWindow 1 1 (-3) (-3) := by
  unfold TreeSchemaSampleWindow treeSchemaResidual treeSchemaDerivativeT
  norm_num

structure TreeImplicitWindow where
  specificationWindow : ℕ
  implicitEquationWindow : ℕ
  singularExpansionWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def treeImplicitReady (w : TreeImplicitWindow) : Prop :=
  0 < w.specificationWindow ∧
    w.singularExpansionWindow ≤
      w.specificationWindow + w.implicitEquationWindow + w.slack

def treeImplicitBudget (w : TreeImplicitWindow) : ℕ :=
  w.specificationWindow + w.implicitEquationWindow +
    w.singularExpansionWindow + w.slack

theorem singularExpansionWindow_le_treeImplicitBudget
    (w : TreeImplicitWindow) :
    w.singularExpansionWindow ≤ treeImplicitBudget w := by
  unfold treeImplicitBudget
  omega

def sampleTreeImplicitWindow : TreeImplicitWindow :=
  { specificationWindow := 4
    implicitEquationWindow := 5
    singularExpansionWindow := 8
    slack := 1 }

example : treeImplicitReady sampleTreeImplicitWindow := by
  norm_num [treeImplicitReady, sampleTreeImplicitWindow]

structure TreeLikeStructuresImplicitFunctionsBudgetCertificate where
  specificationWindow : ℕ
  equationWindow : ℕ
  expansionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TreeLikeStructuresImplicitFunctionsBudgetCertificate.controlled
    (c : TreeLikeStructuresImplicitFunctionsBudgetCertificate) : Prop :=
  0 < c.specificationWindow ∧
    c.expansionWindow ≤ c.specificationWindow + c.equationWindow + c.slack

def TreeLikeStructuresImplicitFunctionsBudgetCertificate.budgetControlled
    (c : TreeLikeStructuresImplicitFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.specificationWindow + c.equationWindow + c.expansionWindow + c.slack

def TreeLikeStructuresImplicitFunctionsBudgetCertificate.Ready
    (c : TreeLikeStructuresImplicitFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TreeLikeStructuresImplicitFunctionsBudgetCertificate.size
    (c : TreeLikeStructuresImplicitFunctionsBudgetCertificate) : ℕ :=
  c.specificationWindow + c.equationWindow + c.expansionWindow + c.slack

theorem treeLikeStructuresImplicitFunctions_budgetCertificate_le_size
    (c : TreeLikeStructuresImplicitFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleTreeLikeStructuresImplicitFunctionsBudgetCertificate :
    TreeLikeStructuresImplicitFunctionsBudgetCertificate :=
  { specificationWindow := 4
    equationWindow := 5
    expansionWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTreeLikeStructuresImplicitFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [TreeLikeStructuresImplicitFunctionsBudgetCertificate.controlled,
      sampleTreeLikeStructuresImplicitFunctionsBudgetCertificate]
  · norm_num [TreeLikeStructuresImplicitFunctionsBudgetCertificate.budgetControlled,
      sampleTreeLikeStructuresImplicitFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTreeLikeStructuresImplicitFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleTreeLikeStructuresImplicitFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleTreeLikeStructuresImplicitFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [TreeLikeStructuresImplicitFunctionsBudgetCertificate.controlled,
      sampleTreeLikeStructuresImplicitFunctionsBudgetCertificate]
  · norm_num
      [TreeLikeStructuresImplicitFunctionsBudgetCertificate.budgetControlled,
        sampleTreeLikeStructuresImplicitFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List TreeLikeStructuresImplicitFunctionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTreeLikeStructuresImplicitFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleTreeLikeStructuresImplicitFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.TreeLikeStructuresImplicitFunctions
