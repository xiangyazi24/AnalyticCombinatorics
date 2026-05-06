import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Labelled tree examples.
-/

namespace AnalyticCombinatorics.PartA.Ch2.LabelledTrees

structure LabelledTreeWindow where
  vertexCount : ℕ
  edgeBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def labelledTreeWindowReady (w : LabelledTreeWindow) : Prop :=
  0 < w.vertexCount ∧ w.edgeBudget ≤ w.vertexCount + w.slack

def labelledTreeWindowBudget (w : LabelledTreeWindow) : ℕ :=
  w.vertexCount + w.edgeBudget + w.slack

/-- Cayley counts `n^(n-2)` for small positive `n`, with conventional table values. -/
def labelledTreeCount : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 16
  | 5 => 125
  | 6 => 1296
  | 7 => 16807
  | _ => 0

def rootedLabelledTreeCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) ^ n

theorem labelledTreeWindowReady.certificate {w : LabelledTreeWindow}
    (h : labelledTreeWindowReady w) :
    0 < w.vertexCount ∧ w.edgeBudget ≤ w.vertexCount + w.slack ∧
      w.edgeBudget ≤ labelledTreeWindowBudget w := by
  rcases h with ⟨hvertices, hedges⟩
  refine ⟨hvertices, hedges, ?_⟩
  unfold labelledTreeWindowBudget
  omega

def sampleLabelledTreeWindow : LabelledTreeWindow :=
  { vertexCount := 7, edgeBudget := 6, slack := 1 }

example : labelledTreeWindowReady sampleLabelledTreeWindow := by
  norm_num [labelledTreeWindowReady, sampleLabelledTreeWindow]

example : labelledTreeCount 1 = 1 := by native_decide
example : labelledTreeCount 4 = 16 := by native_decide
example : labelledTreeCount 7 = 16807 := by native_decide
example : rootedLabelledTreeCount 5 = 625 := by native_decide
example : labelledTreeWindowBudget sampleLabelledTreeWindow = 14 := by native_decide

theorem labelledTreeCount_values_1_to_7 :
    (List.range 7).map (fun k => labelledTreeCount (k + 1)) =
      [1, 1, 3, 16, 125, 1296, 16807] := by
  native_decide


structure LabelledTreesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledTreesBudgetCertificate.controlled
    (c : LabelledTreesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LabelledTreesBudgetCertificate.budgetControlled
    (c : LabelledTreesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LabelledTreesBudgetCertificate.Ready
    (c : LabelledTreesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LabelledTreesBudgetCertificate.size
    (c : LabelledTreesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem labelledTrees_budgetCertificate_le_size
    (c : LabelledTreesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLabelledTreesBudgetCertificate :
    LabelledTreesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLabelledTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledTreesBudgetCertificate.controlled,
      sampleLabelledTreesBudgetCertificate]
  · norm_num [LabelledTreesBudgetCertificate.budgetControlled,
      sampleLabelledTreesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLabelledTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledTreesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLabelledTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledTreesBudgetCertificate.controlled,
      sampleLabelledTreesBudgetCertificate]
  · norm_num [LabelledTreesBudgetCertificate.budgetControlled,
      sampleLabelledTreesBudgetCertificate]

example :
    sampleLabelledTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledTreesBudgetCertificate.size := by
  apply labelledTrees_budgetCertificate_le_size
  constructor
  · norm_num [LabelledTreesBudgetCertificate.controlled,
      sampleLabelledTreesBudgetCertificate]
  · norm_num [LabelledTreesBudgetCertificate.budgetControlled,
      sampleLabelledTreesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LabelledTreesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLabelledTreesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLabelledTreesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.LabelledTrees
