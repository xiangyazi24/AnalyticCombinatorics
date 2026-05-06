import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Tree, word, and language models.

Finite windows linking words, regular/context-free languages, and tree
specifications in symbolic enumeration.
-/

namespace AnalyticCombinatorics.PartA.Ch1.TreeWordLanguageModels

/-- Binary tree leaves encoded by binary words of bounded height. -/
def binaryWordsAtHeight (height : ℕ) : ℕ :=
  2 ^ height

/-- Full binary tree node count at a bounded height. -/
def fullBinaryTreeNodes (height : ℕ) : ℕ :=
  2 ^ (height + 1) - 1

/-- Finite language/tree envelope linking words and complete binary trees. -/
def treeWordEnvelopeCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun h =>
    binaryWordsAtHeight h ≤ fullBinaryTreeNodes h + 1

theorem treeWordEnvelope_window :
    treeWordEnvelopeCheck 16 = true := by
  unfold treeWordEnvelopeCheck binaryWordsAtHeight fullBinaryTreeNodes
  native_decide

structure TreeWordLanguageData where
  alphabetSize : ℕ
  wordLength : ℕ
  grammarRules : ℕ
  treeHeight : ℕ
  languageSlack : ℕ
deriving DecidableEq, Repr

def hasAlphabet (d : TreeWordLanguageData) : Prop :=
  0 < d.alphabetSize

def grammarRulesControlled (d : TreeWordLanguageData) : Prop :=
  d.grammarRules ≤ d.alphabetSize * (d.wordLength + 1) + d.languageSlack

def treeHeightControlled (d : TreeWordLanguageData) : Prop :=
  d.treeHeight ≤ d.wordLength + d.grammarRules + d.languageSlack

def treeWordLanguageReady (d : TreeWordLanguageData) : Prop :=
  hasAlphabet d ∧ grammarRulesControlled d ∧ treeHeightControlled d

def treeWordLanguageBudget (d : TreeWordLanguageData) : ℕ :=
  d.alphabetSize + d.wordLength + d.grammarRules + d.treeHeight + d.languageSlack

theorem treeHeight_le_budget (d : TreeWordLanguageData) :
    d.treeHeight ≤ treeWordLanguageBudget d := by
  unfold treeWordLanguageBudget
  omega

def sampleTreeWordLanguageData : TreeWordLanguageData :=
  { alphabetSize := 2
    wordLength := 5
    grammarRules := 8
    treeHeight := 6
    languageSlack := 1 }

example : treeWordLanguageReady sampleTreeWordLanguageData := by
  constructor
  · norm_num [hasAlphabet, sampleTreeWordLanguageData]
  constructor
  · norm_num [grammarRulesControlled, sampleTreeWordLanguageData]
  · norm_num [treeHeightControlled, sampleTreeWordLanguageData]

structure TreeWordLanguageModelsBudgetCertificate where
  alphabetWindow : ℕ
  wordWindow : ℕ
  grammarWindow : ℕ
  treeWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TreeWordLanguageModelsBudgetCertificate.controlled
    (c : TreeWordLanguageModelsBudgetCertificate) : Prop :=
  0 < c.alphabetWindow ∧
    c.grammarWindow ≤ c.alphabetWindow * (c.wordWindow + 1) + c.slack ∧
      c.treeWindow ≤ c.wordWindow + c.grammarWindow + c.slack

def TreeWordLanguageModelsBudgetCertificate.budgetControlled
    (c : TreeWordLanguageModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.alphabetWindow + c.wordWindow + c.grammarWindow + c.treeWindow + c.slack

def TreeWordLanguageModelsBudgetCertificate.Ready
    (c : TreeWordLanguageModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TreeWordLanguageModelsBudgetCertificate.size
    (c : TreeWordLanguageModelsBudgetCertificate) : ℕ :=
  c.alphabetWindow + c.wordWindow + c.grammarWindow + c.treeWindow + c.slack

theorem treeWordLanguageModels_budgetCertificate_le_size
    (c : TreeWordLanguageModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleTreeWordLanguageModelsBudgetCertificate :
    TreeWordLanguageModelsBudgetCertificate :=
  { alphabetWindow := 2
    wordWindow := 5
    grammarWindow := 8
    treeWindow := 6
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTreeWordLanguageModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [TreeWordLanguageModelsBudgetCertificate.controlled,
      sampleTreeWordLanguageModelsBudgetCertificate]
  · norm_num [TreeWordLanguageModelsBudgetCertificate.budgetControlled,
      sampleTreeWordLanguageModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTreeWordLanguageModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleTreeWordLanguageModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleTreeWordLanguageModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [TreeWordLanguageModelsBudgetCertificate.controlled,
      sampleTreeWordLanguageModelsBudgetCertificate]
  · norm_num [TreeWordLanguageModelsBudgetCertificate.budgetControlled,
      sampleTreeWordLanguageModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List TreeWordLanguageModelsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleTreeWordLanguageModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleTreeWordLanguageModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.TreeWordLanguageModels
