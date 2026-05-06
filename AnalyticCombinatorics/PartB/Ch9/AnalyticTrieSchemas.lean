import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic schemas for tries and digital trees.

This file keeps the finite arity/depth checks separate from the Mellin and
depoissonization estimates used in full trie analysis.
-/

namespace AnalyticCombinatorics.PartB.Ch9.AnalyticTrieSchemas

structure TrieSchemaData where
  alphabetSize : ℕ
  depth : ℕ
  tollBound : ℕ
deriving DecidableEq, Repr

def positiveAlphabet (d : TrieSchemaData) : Prop :=
  0 < d.alphabetSize

def trieAdmissible (d : TrieSchemaData) : Prop :=
  positiveAlphabet d ∧ d.tollBound ≤ d.alphabetSize ^ (d.depth + 1)

def nodeBudget (alphabet depth : ℕ) : ℕ :=
  alphabet ^ depth

theorem nodeBudget_positive {alphabet depth : ℕ}
    (h : 0 < alphabet) :
    0 < nodeBudget alphabet depth := by
  unfold nodeBudget
  exact pow_pos h depth

theorem trieAdmissible.alphabet {d : TrieSchemaData}
    (h : trieAdmissible d) :
    positiveAlphabet d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

def sampleTrie : TrieSchemaData :=
  { alphabetSize := 2, depth := 4, tollBound := 9 }

example : trieAdmissible sampleTrie := by
  norm_num [trieAdmissible, positiveAlphabet, sampleTrie]

example : nodeBudget 2 5 = 32 := by
  native_decide

/-- Finite executable readiness audit for analytic trie schema data. -/
def trieSchemaListReady (schemas : List TrieSchemaData) : Bool :=
  schemas.all fun d =>
    0 < d.alphabetSize && d.tollBound ≤ d.alphabetSize ^ (d.depth + 1)

theorem trieSchemaList_readyWindow :
    trieSchemaListReady
      [{ alphabetSize := 2, depth := 3, tollBound := 8 },
       { alphabetSize := 2, depth := 4, tollBound := 9 }] = true := by
  unfold trieSchemaListReady
  native_decide

structure TrieWindow where
  alphabetSize : ℕ
  depth : ℕ
  nodeCount : ℕ
  tollBound : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TrieWindow.alphabetReady (w : TrieWindow) : Prop :=
  0 < w.alphabetSize

def TrieWindow.nodeControlled (w : TrieWindow) : Prop :=
  w.nodeCount ≤ w.alphabetSize ^ (w.depth + 1) + w.slack

def TrieWindow.tollControlled (w : TrieWindow) : Prop :=
  w.tollBound ≤ w.nodeCount + w.slack

def TrieWindow.ready (w : TrieWindow) : Prop :=
  w.alphabetReady ∧ w.nodeControlled ∧ w.tollControlled

def TrieWindow.certificate (w : TrieWindow) : ℕ :=
  w.alphabetSize + w.depth + w.nodeCount + w.tollBound + w.slack

theorem tollBound_le_certificate (w : TrieWindow) :
    w.tollBound ≤ w.certificate := by
  unfold TrieWindow.certificate
  omega

def sampleTrieWindow : TrieWindow :=
  { alphabetSize := 2, depth := 4, nodeCount := 16, tollBound := 9, slack := 0 }

example : sampleTrieWindow.ready := by
  norm_num [sampleTrieWindow, TrieWindow.ready, TrieWindow.alphabetReady,
    TrieWindow.nodeControlled, TrieWindow.tollControlled]


structure AnalyticTrieSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticTrieSchemasBudgetCertificate.controlled
    (c : AnalyticTrieSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticTrieSchemasBudgetCertificate.budgetControlled
    (c : AnalyticTrieSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticTrieSchemasBudgetCertificate.Ready
    (c : AnalyticTrieSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticTrieSchemasBudgetCertificate.size
    (c : AnalyticTrieSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticTrieSchemas_budgetCertificate_le_size
    (c : AnalyticTrieSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticTrieSchemasBudgetCertificate :
    AnalyticTrieSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAnalyticTrieSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticTrieSchemasBudgetCertificate.controlled,
      sampleAnalyticTrieSchemasBudgetCertificate]
  · norm_num [AnalyticTrieSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticTrieSchemasBudgetCertificate]

example :
    sampleAnalyticTrieSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticTrieSchemasBudgetCertificate.size := by
  apply analyticTrieSchemas_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticTrieSchemasBudgetCertificate.controlled,
      sampleAnalyticTrieSchemasBudgetCertificate]
  · norm_num [AnalyticTrieSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticTrieSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAnalyticTrieSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticTrieSchemasBudgetCertificate.controlled,
      sampleAnalyticTrieSchemasBudgetCertificate]
  · norm_num [AnalyticTrieSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticTrieSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticTrieSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticTrieSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AnalyticTrieSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticTrieSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticTrieSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.AnalyticTrieSchemas
