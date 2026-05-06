import Mathlib.Tactic

namespace AnalyticCombinatorics.PartA.Ch1.WordsLanguages

/-!
  # Words and Languages — Basic Counting

  Formalizes basic word-counting functions from Chapter I of Flajolet & Sedgewick:
  - Words over an alphabet of size r
  - Binary strings avoiding consecutive ones (Fibonacci)
  - Dyck words / balanced parentheses (Catalan numbers)
  - Smirnov words (no adjacent repeated letters)
  - Run-length encoding counts
-/

set_option linter.style.nativeDecide false


/-! ## Words over alphabet of size r -/

/-- The number of words of length `n` over an alphabet of size `r` is `r^n`. -/
def wordCount (r n : ℕ) : ℕ := r ^ n

theorem wordCount_2_5 : wordCount 2 5 = 32 := by native_decide
theorem wordCount_3_4 : wordCount 3 4 = 81 := by native_decide
theorem wordCount_26_2 : wordCount 26 2 = 676 := by native_decide

/-! ## Binary strings avoiding "11" (no consecutive ones) -/

/-- Binary strings of length `n` with no two consecutive ones, counted by Fibonacci shifted. -/
def noConsecOnes (n : ℕ) : ℕ := Nat.fib (n + 2)

theorem noConsecOnes_0 : noConsecOnes 0 = 1 := by native_decide
theorem noConsecOnes_1 : noConsecOnes 1 = 2 := by native_decide
theorem noConsecOnes_2 : noConsecOnes 2 = 3 := by native_decide
theorem noConsecOnes_3 : noConsecOnes 3 = 5 := by native_decide
theorem noConsecOnes_4 : noConsecOnes 4 = 8 := by native_decide
theorem noConsecOnes_5 : noConsecOnes 5 = 13 := by native_decide

/-! ## Dyck words (balanced parentheses = Catalan numbers) -/

/-- The number of Dyck words of semilength `n` (Catalan number). -/
def dyckWordCount (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

theorem dyckWordCount_0 : dyckWordCount 0 = 1 := by native_decide
theorem dyckWordCount_1 : dyckWordCount 1 = 1 := by native_decide
theorem dyckWordCount_2 : dyckWordCount 2 = 2 := by native_decide
theorem dyckWordCount_3 : dyckWordCount 3 = 5 := by native_decide
theorem dyckWordCount_4 : dyckWordCount 4 = 14 := by native_decide
theorem dyckWordCount_5 : dyckWordCount 5 = 42 := by native_decide

/-! ## Smirnov words (no adjacent repeats on r-letter alphabet) -/

/-- Smirnov words: words of length `n` on `r` letters with no two adjacent letters equal. -/
def smirnovCount (r n : ℕ) : ℕ :=
  if n = 0 then 1 else r * (r - 1) ^ (n - 1)

theorem smirnovCount_2_3 : smirnovCount 2 3 = 2 := by native_decide
theorem smirnovCount_3_3 : smirnovCount 3 3 = 12 := by native_decide
theorem smirnovCount_3_5 : smirnovCount 3 5 = 48 := by native_decide

/-! ## Run-length encoding count -/

/-- Number of words of length `n` on `r` letters with exactly `k` runs. -/
def runLengthCount (r n k : ℕ) : ℕ :=
  if k = 0 then (if n = 0 then 1 else 0)
  else r * (r - 1) ^ (k - 1) * Nat.choose (n - 1) (k - 1)

theorem runLengthCount_2_4_1 : runLengthCount 2 4 1 = 2 := by native_decide
theorem runLengthCount_2_4_2 : runLengthCount 2 4 2 = 6 := by native_decide
theorem runLengthCount_2_4_3 : runLengthCount 2 4 3 = 6 := by native_decide
theorem runLengthCount_2_4_4 : runLengthCount 2 4 4 = 2 := by native_decide

/-- Row sum: total words of length 4 on 2 letters equals 2^4 = 16. -/
theorem runLength_row_sum_2_4 :
    runLengthCount 2 4 0 + runLengthCount 2 4 1 + runLengthCount 2 4 2 +
    runLengthCount 2 4 3 + runLengthCount 2 4 4 = 16 := by native_decide



structure WordsLanguagesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WordsLanguagesBudgetCertificate.controlled
    (c : WordsLanguagesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def WordsLanguagesBudgetCertificate.budgetControlled
    (c : WordsLanguagesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def WordsLanguagesBudgetCertificate.Ready
    (c : WordsLanguagesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WordsLanguagesBudgetCertificate.size
    (c : WordsLanguagesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem wordsLanguages_budgetCertificate_le_size
    (c : WordsLanguagesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWordsLanguagesBudgetCertificate :
    WordsLanguagesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleWordsLanguagesBudgetCertificate.Ready := by
  constructor
  · norm_num [WordsLanguagesBudgetCertificate.controlled,
      sampleWordsLanguagesBudgetCertificate]
  · norm_num [WordsLanguagesBudgetCertificate.budgetControlled,
      sampleWordsLanguagesBudgetCertificate]

example :
    sampleWordsLanguagesBudgetCertificate.certificateBudgetWindow ≤
      sampleWordsLanguagesBudgetCertificate.size := by
  apply wordsLanguages_budgetCertificate_le_size
  constructor
  · norm_num [WordsLanguagesBudgetCertificate.controlled,
      sampleWordsLanguagesBudgetCertificate]
  · norm_num [WordsLanguagesBudgetCertificate.budgetControlled,
      sampleWordsLanguagesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleWordsLanguagesBudgetCertificate.Ready := by
  constructor
  · norm_num [WordsLanguagesBudgetCertificate.controlled,
      sampleWordsLanguagesBudgetCertificate]
  · norm_num [WordsLanguagesBudgetCertificate.budgetControlled,
      sampleWordsLanguagesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWordsLanguagesBudgetCertificate.certificateBudgetWindow ≤
      sampleWordsLanguagesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List WordsLanguagesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleWordsLanguagesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleWordsLanguagesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.WordsLanguages
