import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Words and regular languages
-/

namespace AnalyticCombinatorics.PartA.Ch1.WordsAndRegularLanguages

/-- Number of words of length `n` over an alphabet of size `q`. -/
def wordCount (q n : ℕ) : ℕ :=
  q ^ n

theorem wordCount_zero_length (q : ℕ) :
    wordCount q 0 = 1 := by
  simp [wordCount]

theorem wordCount_succ (q n : ℕ) :
    wordCount q (n + 1) = q * wordCount q n := by
  simp [wordCount, pow_succ, Nat.mul_comm]

/-- Binary words with no consecutive ones, indexed by length. -/
def noConsecutiveOnesCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => noConsecutiveOnesCount (n + 1) + noConsecutiveOnesCount n

theorem noConsecutiveOnesCount_samples :
    noConsecutiveOnesCount 0 = 1 ∧
      noConsecutiveOnesCount 1 = 2 ∧
        noConsecutiveOnesCount 4 = 8 := by
  native_decide

/-- Deterministic finite automaton transition table over a finite state set. -/
structure DFA where
  states : ℕ
  alphabet : ℕ
  start : ℕ
  acceptCount : ℕ
deriving DecidableEq, Repr

def DFA.ready (d : DFA) : Prop :=
  0 < d.states ∧ 0 < d.alphabet ∧ d.start < d.states ∧
    d.acceptCount ≤ d.states

theorem sampleDFA_ready :
    DFA.ready { states := 2, alphabet := 2, start := 0, acceptCount := 1 } := by
  norm_num [DFA.ready]

structure BudgetCertificate where
  wordWindow : ℕ
  languageWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.wordWindow ∧ c.languageWindow ≤ c.wordWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.wordWindow + c.languageWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.wordWindow + c.languageWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { wordWindow := 5, languageWindow := 6, certificateBudgetWindow := 12,
    slack := 1 }

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

end AnalyticCombinatorics.PartA.Ch1.WordsAndRegularLanguages
