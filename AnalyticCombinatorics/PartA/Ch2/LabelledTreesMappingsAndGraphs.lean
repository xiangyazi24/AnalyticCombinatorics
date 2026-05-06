import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Labelled trees, mappings, and graphs
-/

namespace AnalyticCombinatorics.PartA.Ch2.LabelledTreesMappingsAndGraphs

/-- Cayley's labelled tree count, with conventional small cases. -/
def cayleyTreeCount : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 2) ^ n

theorem cayleyTreeCount_samples :
    cayleyTreeCount 1 = 1 ∧
      cayleyTreeCount 3 = 3 ∧
        cayleyTreeCount 5 = 125 := by
  native_decide

/-- Endofunctions on an `n`-set. -/
def mappingCount (n : ℕ) : ℕ :=
  n ^ n

theorem mappingCount_zero :
    mappingCount 0 = 1 := by
  simp [mappingCount]

theorem mappingCount_samples :
    mappingCount 3 = 27 ∧ mappingCount 4 = 256 := by
  native_decide

/-- Simple labelled graph count on `n` vertices. -/
def simpleGraphCount (n : ℕ) : ℕ :=
  2 ^ (n.choose 2)

theorem simpleGraphCount_samples :
    simpleGraphCount 3 = 8 ∧ simpleGraphCount 4 = 64 := by
  native_decide

structure BudgetCertificate where
  treeWindow : ℕ
  mappingWindow : ℕ
  graphWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.treeWindow ∧
    c.graphWindow ≤ c.treeWindow + c.mappingWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.treeWindow + c.mappingWindow + c.graphWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.treeWindow + c.mappingWindow + c.graphWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { treeWindow := 5, mappingWindow := 4, graphWindow := 10,
    certificateBudgetWindow := 20, slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartA.Ch2.LabelledTreesMappingsAndGraphs
