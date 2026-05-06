import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Lempel-Ziv limit schemas.

This module records finite bookkeeping for LZ phrase-count windows: an
alphabet size and input length control phrase and dictionary budgets.
-/

namespace AnalyticCombinatorics.PartB.Ch9.LempelZivLimitSchemas

def dictionaryCapacity (alphabetSize depth : ℕ) : ℕ :=
  alphabetSize ^ (depth + 1)

theorem dictionaryCapacity_samples :
    dictionaryCapacity 2 0 = 2 ∧
    dictionaryCapacity 2 3 = 16 ∧
    dictionaryCapacity 3 2 = 27 := by
  native_decide

structure LempelZivLimitData where
  alphabetSize : ℕ
  inputLength : ℕ
  phraseWindow : ℕ
  dictionarySlack : ℕ
deriving DecidableEq, Repr

def hasNontrivialAlphabet (d : LempelZivLimitData) : Prop :=
  1 < d.alphabetSize

def phraseWindowControlled (d : LempelZivLimitData) : Prop :=
  d.phraseWindow ≤ d.inputLength + d.dictionarySlack

def dictionaryWindowControlled (d : LempelZivLimitData) : Prop :=
  d.phraseWindow ≤ dictionaryCapacity d.alphabetSize d.inputLength + d.dictionarySlack

def lempelZivLimitReady (d : LempelZivLimitData) : Prop :=
  hasNontrivialAlphabet d ∧ phraseWindowControlled d ∧ dictionaryWindowControlled d

def lempelZivLimitBudget (d : LempelZivLimitData) : ℕ :=
  d.alphabetSize + d.inputLength + d.phraseWindow + d.dictionarySlack

theorem lempelZivLimitReady.alphabet
    {d : LempelZivLimitData} (h : lempelZivLimitReady d) :
    hasNontrivialAlphabet d := by
  exact h.1

theorem phraseWindow_le_budget (d : LempelZivLimitData) :
    d.phraseWindow ≤ lempelZivLimitBudget d := by
  unfold lempelZivLimitBudget
  omega

def sampleLempelZivLimitData : LempelZivLimitData :=
  { alphabetSize := 2, inputLength := 8, phraseWindow := 5, dictionarySlack := 1 }

example : lempelZivLimitReady sampleLempelZivLimitData := by
  constructor
  · norm_num [hasNontrivialAlphabet, sampleLempelZivLimitData]
  constructor
  · norm_num [phraseWindowControlled, sampleLempelZivLimitData]
  · norm_num [dictionaryWindowControlled, dictionaryCapacity,
      sampleLempelZivLimitData]

example : lempelZivLimitBudget sampleLempelZivLimitData = 16 := by
  native_decide

/-- Finite executable readiness audit for Lempel-Ziv limit windows. -/
def lempelZivLimitListReady
    (windows : List LempelZivLimitData) : Bool :=
  windows.all fun d =>
    1 < d.alphabetSize &&
      d.phraseWindow ≤ d.inputLength + d.dictionarySlack &&
        d.phraseWindow ≤ dictionaryCapacity d.alphabetSize d.inputLength +
          d.dictionarySlack

theorem lempelZivLimitList_readyWindow :
    lempelZivLimitListReady
      [{ alphabetSize := 2, inputLength := 4, phraseWindow := 3,
         dictionarySlack := 1 },
       { alphabetSize := 2, inputLength := 8, phraseWindow := 5,
         dictionarySlack := 1 }] = true := by
  unfold lempelZivLimitListReady dictionaryCapacity
  native_decide

structure LempelZivLimitBudgetCertificate where
  alphabetWindow : ℕ
  lengthWindow : ℕ
  phraseWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LempelZivLimitBudgetCertificate.controlled
    (c : LempelZivLimitBudgetCertificate) : Prop :=
  1 < c.alphabetWindow ∧
    c.phraseWindow ≤ c.lengthWindow + c.slack

def LempelZivLimitBudgetCertificate.budgetControlled
    (c : LempelZivLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.alphabetWindow + c.lengthWindow + c.phraseWindow + c.slack

def LempelZivLimitBudgetCertificate.Ready
    (c : LempelZivLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LempelZivLimitBudgetCertificate.size
    (c : LempelZivLimitBudgetCertificate) : ℕ :=
  c.alphabetWindow + c.lengthWindow + c.phraseWindow + c.slack

theorem lempelZivLimit_budgetCertificate_le_size
    (c : LempelZivLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLempelZivLimitBudgetCertificate :
    LempelZivLimitBudgetCertificate :=
  { alphabetWindow := 2
    lengthWindow := 8
    phraseWindow := 5
    certificateBudgetWindow := 16
    slack := 1 }

example : sampleLempelZivLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [LempelZivLimitBudgetCertificate.controlled,
      sampleLempelZivLimitBudgetCertificate]
  · norm_num [LempelZivLimitBudgetCertificate.budgetControlled,
      sampleLempelZivLimitBudgetCertificate]

example :
    sampleLempelZivLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleLempelZivLimitBudgetCertificate.size := by
  apply lempelZivLimit_budgetCertificate_le_size
  constructor
  · norm_num [LempelZivLimitBudgetCertificate.controlled,
      sampleLempelZivLimitBudgetCertificate]
  · norm_num [LempelZivLimitBudgetCertificate.budgetControlled,
      sampleLempelZivLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLempelZivLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [LempelZivLimitBudgetCertificate.controlled,
      sampleLempelZivLimitBudgetCertificate]
  · norm_num [LempelZivLimitBudgetCertificate.budgetControlled,
      sampleLempelZivLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLempelZivLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleLempelZivLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LempelZivLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLempelZivLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLempelZivLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.LempelZivLimitSchemas
