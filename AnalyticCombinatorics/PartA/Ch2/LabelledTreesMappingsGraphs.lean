import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Labelled trees, mappings, and graphs.
-/

namespace AnalyticCombinatorics.PartA.Ch2.LabelledTreesMappingsGraphs

/-- Cayley labelled-tree count, with the small cases made explicit. -/
def cayleyTreeCount : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 2) ^ n

/-- Endofunction count on an `n`-element labelled set. -/
def mappingCount (n : ℕ) : ℕ :=
  n ^ n

/-- Simple labelled graph count on an `n`-element vertex set. -/
def simpleGraphCount (n : ℕ) : ℕ :=
  2 ^ (n * (n - 1) / 2)

/-- Finite dominance audit for labelled tree, mapping, and graph counts. -/
def labelledTreeMappingGraphCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    cayleyTreeCount n ≤ mappingCount n ∧ 1 ≤ simpleGraphCount n

theorem cayleyTreeCount_samples :
    cayleyTreeCount 1 = 1 ∧
    cayleyTreeCount 2 = 1 ∧
    cayleyTreeCount 3 = 3 ∧
    cayleyTreeCount 4 = 16 ∧
    cayleyTreeCount 5 = 125 := by
  native_decide

theorem labelledTreeMappingGraph_window :
    labelledTreeMappingGraphCheck 12 = true := by
  unfold labelledTreeMappingGraphCheck cayleyTreeCount mappingCount
    simpleGraphCount
  native_decide

/-- Prefix sum of the labelled-tree sample counts. -/
def cayleyTreePrefixSum (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + cayleyTreeCount n) 0

def CayleyTreePrefixWindow (N total : ℕ) : Prop :=
  cayleyTreePrefixSum N = total

theorem cayleyTree_prefixWindow :
    CayleyTreePrefixWindow 5 146 := by
  unfold CayleyTreePrefixWindow cayleyTreePrefixSum cayleyTreeCount
  native_decide

example : mappingCount 4 = 256 := by
  unfold mappingCount
  native_decide

example : simpleGraphCount 5 = 1024 := by
  unfold simpleGraphCount
  native_decide

structure LabelledTreesMappingsGraphsBudgetCertificate where
  treeWindow : ℕ
  mappingWindow : ℕ
  graphWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledTreesMappingsGraphsBudgetCertificate.controlled
    (c : LabelledTreesMappingsGraphsBudgetCertificate) : Prop :=
  0 < c.treeWindow ∧ c.graphWindow ≤ c.treeWindow + c.mappingWindow + c.slack

def LabelledTreesMappingsGraphsBudgetCertificate.budgetControlled
    (c : LabelledTreesMappingsGraphsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.treeWindow + c.mappingWindow + c.graphWindow + c.slack

def LabelledTreesMappingsGraphsBudgetCertificate.Ready
    (c : LabelledTreesMappingsGraphsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LabelledTreesMappingsGraphsBudgetCertificate.size
    (c : LabelledTreesMappingsGraphsBudgetCertificate) : ℕ :=
  c.treeWindow + c.mappingWindow + c.graphWindow + c.slack

theorem labelledTreesMappingsGraphs_budgetCertificate_le_size
    (c : LabelledTreesMappingsGraphsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleLabelledTreesMappingsGraphsBudgetCertificate :
    LabelledTreesMappingsGraphsBudgetCertificate :=
  { treeWindow := 5
    mappingWindow := 6
    graphWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLabelledTreesMappingsGraphsBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledTreesMappingsGraphsBudgetCertificate.controlled,
      sampleLabelledTreesMappingsGraphsBudgetCertificate]
  · norm_num [LabelledTreesMappingsGraphsBudgetCertificate.budgetControlled,
      sampleLabelledTreesMappingsGraphsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLabelledTreesMappingsGraphsBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledTreesMappingsGraphsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLabelledTreesMappingsGraphsBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledTreesMappingsGraphsBudgetCertificate.controlled,
      sampleLabelledTreesMappingsGraphsBudgetCertificate]
  · norm_num [LabelledTreesMappingsGraphsBudgetCertificate.budgetControlled,
      sampleLabelledTreesMappingsGraphsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List LabelledTreesMappingsGraphsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLabelledTreesMappingsGraphsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLabelledTreesMappingsGraphsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.LabelledTreesMappingsGraphs
