import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Words and regular languages.
-/

namespace AnalyticCombinatorics.PartA.Ch1.WordsRegularLanguages

/-- Word count over a finite alphabet. -/
def wordCount (alphabet length : ℕ) : ℕ :=
  alphabet ^ length

/-- A regular-language model with one accepted word for each final state. -/
def regularLanguageProxy (states length : ℕ) : ℕ :=
  Nat.min (length + 1) (states * (length + 1))

/-- Finite regular-language envelope by all words over the alphabet. -/
def regularLanguageEnvelopeCheck
    (alphabet states N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    regularLanguageProxy states n ≤ wordCount alphabet n

theorem binaryWordCount_samples :
    wordCount 2 0 = 1 ∧
    wordCount 2 1 = 2 ∧
    wordCount 2 2 = 4 ∧
    wordCount 2 3 = 8 := by
  unfold wordCount
  native_decide

theorem regularLanguageEnvelope_binary :
    regularLanguageEnvelopeCheck 2 1 12 = true := by
  unfold regularLanguageEnvelopeCheck regularLanguageProxy wordCount
  native_decide

/-- Prefix count of all words up to a finite length. -/
def wordPrefixCount (alphabet N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total n => total + wordCount alphabet n) 0

def WordPrefixWindow (alphabet N total : ℕ) : Prop :=
  wordPrefixCount alphabet N = total

theorem binaryWordPrefix_window :
    WordPrefixWindow 2 4 31 := by
  unfold WordPrefixWindow wordPrefixCount wordCount
  native_decide

example : wordCount 3 4 = 81 := by
  unfold wordCount
  native_decide

example : wordPrefixCount 3 3 = 40 := by
  unfold wordPrefixCount wordCount
  native_decide

structure WordsRegularLanguagesBudgetCertificate where
  alphabetWindow : ℕ
  automatonWindow : ℕ
  languageWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WordsRegularLanguagesBudgetCertificate.controlled
    (c : WordsRegularLanguagesBudgetCertificate) : Prop :=
  0 < c.alphabetWindow ∧
    c.languageWindow ≤ c.alphabetWindow + c.automatonWindow + c.slack

def WordsRegularLanguagesBudgetCertificate.budgetControlled
    (c : WordsRegularLanguagesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.alphabetWindow + c.automatonWindow + c.languageWindow + c.slack

def WordsRegularLanguagesBudgetCertificate.Ready
    (c : WordsRegularLanguagesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WordsRegularLanguagesBudgetCertificate.size
    (c : WordsRegularLanguagesBudgetCertificate) : ℕ :=
  c.alphabetWindow + c.automatonWindow + c.languageWindow + c.slack

theorem wordsRegularLanguages_budgetCertificate_le_size
    (c : WordsRegularLanguagesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleWordsRegularLanguagesBudgetCertificate :
    WordsRegularLanguagesBudgetCertificate :=
  { alphabetWindow := 5
    automatonWindow := 6
    languageWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleWordsRegularLanguagesBudgetCertificate.Ready := by
  constructor
  · norm_num [WordsRegularLanguagesBudgetCertificate.controlled,
      sampleWordsRegularLanguagesBudgetCertificate]
  · norm_num [WordsRegularLanguagesBudgetCertificate.budgetControlled,
      sampleWordsRegularLanguagesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWordsRegularLanguagesBudgetCertificate.certificateBudgetWindow ≤
      sampleWordsRegularLanguagesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleWordsRegularLanguagesBudgetCertificate.Ready := by
  constructor
  · norm_num [WordsRegularLanguagesBudgetCertificate.controlled,
      sampleWordsRegularLanguagesBudgetCertificate]
  · norm_num [WordsRegularLanguagesBudgetCertificate.budgetControlled,
      sampleWordsRegularLanguagesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List WordsRegularLanguagesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleWordsRegularLanguagesBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleWordsRegularLanguagesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.WordsRegularLanguages
