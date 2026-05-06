import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.AutomataEnumeration


open Finset

/-! ## 1. Binary strings of length n -/

/-- Number of binary strings of length `n`. -/
def binaryStrings (n : ℕ) : ℕ := 2 ^ n

/-- Values of `2^n` for `n = 0..10`. -/
def binaryStringsTable : Fin 11 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

example : ∀ n : Fin 11, binaryStringsTable n = binaryStrings n.1 := by native_decide

/-! ## 2. Binary strings avoiding `11` -/

/-- Number of binary strings of length `n` with no two consecutive ones. -/
def avoid11 (n : ℕ) : ℕ := Nat.fib (n + 2)

/-- Values for `n = 0..8`: `F(n+2)`. -/
def avoid11Table : Fin 9 → ℕ :=
  ![1, 2, 3, 5, 8, 13, 21, 34, 55]

/-- The shifted Fibonacci table `F(n+2)` for `n = 0..8`. -/
def shiftedFibTable : Fin 9 → ℕ :=
  ![1, 2, 3, 5, 8, 13, 21, 34, 55]

example : ∀ n : Fin 9, avoid11Table n = shiftedFibTable n := by native_decide
example : ∀ n : Fin 9, avoid11Table n = avoid11 n.1 := by native_decide

/-! ## 3. Strings over a k-letter alphabet -/

/-- Number of length-`n` words over an alphabet of size `k`. -/
def alphabetStrings (k n : ℕ) : ℕ := k ^ n

/-- Values of `3^n` for `n = 0..6`. -/
def ternaryStringsTable : Fin 7 → ℕ :=
  ![1, 3, 9, 27, 81, 243, 729]

example : ∀ n : Fin 7, ternaryStringsTable n = alphabetStrings 3 n.1 := by native_decide

/-! ## 4. Binary strings with exactly k ones -/

/-- Number of binary strings of length `n` with exactly `k` ones. -/
def binaryStringsWithKOnes (n k : ℕ) : ℕ := Nat.choose n k

/-- Row `n = 8` of Pascal's triangle. -/
def choose8Table : Fin 9 → ℕ :=
  ![1, 8, 28, 56, 70, 56, 28, 8, 1]

example : ∀ k : Fin 9, choose8Table k = binaryStringsWithKOnes 8 k.1 := by native_decide

example :
    choose8Table ⟨0, by omega⟩ + choose8Table ⟨1, by omega⟩
      + choose8Table ⟨2, by omega⟩ + choose8Table ⟨3, by omega⟩
      + choose8Table ⟨4, by omega⟩ + choose8Table ⟨5, by omega⟩
      + choose8Table ⟨6, by omega⟩ + choose8Table ⟨7, by omega⟩
      + choose8Table ⟨8, by omega⟩ = 256 := by
  native_decide

example :
    choose8Table ⟨0, by omega⟩ + choose8Table ⟨1, by omega⟩
      + choose8Table ⟨2, by omega⟩ + choose8Table ⟨3, by omega⟩
      + choose8Table ⟨4, by omega⟩ + choose8Table ⟨5, by omega⟩
      + choose8Table ⟨6, by omega⟩ + choose8Table ⟨7, by omega⟩
      + choose8Table ⟨8, by omega⟩ = 2 ^ 8 := by
  native_decide

/-! ## 5. Distinct subsequences and binomial layers -/

/-- Number of subsets of positions in a binary string of length `n`. -/
def subsequencePositionBound (n : ℕ) : ℕ := 2 ^ n

/-- Position-subset bounds for `n = 0..8`. -/
def subsequencePositionBoundTable : Fin 9 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256]

example :
    ∀ n : Fin 9, subsequencePositionBoundTable n = subsequencePositionBound n.1 := by
  native_decide

/-- Factorials `0!` through `8!`. -/
def factorialTable : Fin 9 → ℕ :=
  ![1, 1, 2, 6, 24, 120, 720, 5040, 40320]

example : ∀ n : Fin 9, factorialTable n = Nat.factorial n.1 := by native_decide

/-- Binomial coefficient as the factorial quotient. -/
def factorialQuotient (n k : ℕ) : ℕ :=
  Nat.factorial n / (Nat.factorial k * Nat.factorial (n - k))

example : factorialQuotient 4 2 = Nat.choose 4 2 := by native_decide
example : factorialQuotient 5 3 = Nat.choose 5 3 := by native_decide
example : factorialQuotient 6 2 = Nat.choose 6 2 := by native_decide
example : factorialQuotient 7 4 = Nat.choose 7 4 := by native_decide
example : factorialQuotient 8 0 = Nat.choose 8 0 := by native_decide
example : factorialQuotient 8 4 = Nat.choose 8 4 := by native_decide
example : factorialQuotient 8 8 = Nat.choose 8 8 := by native_decide

/-! ## 6. Binary necklaces under rotation -/

/-- Euler phi values needed for the divisor sums through length `6`. -/
def phiSmall : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 4
  | 6 => 2
  | _ => 0

/-- Binary-necklace Burnside formula for the checked lengths. -/
def binaryNecklaceFormula (n : ℕ) : ℕ :=
  ((range (n + 1)).filter fun d => d ∣ n).sum
      (fun d => phiSmall (n / d) * 2 ^ d) / n

/-- Binary necklaces of length `n = 1..6`. -/
def binaryNecklaceTable : Fin 6 → ℕ :=
  ![2, 3, 4, 6, 8, 14]

example : ∀ n : Fin 6, binaryNecklaceTable n = binaryNecklaceFormula (n.1 + 1) := by
  native_decide

example : binaryNecklaceTable ⟨0, by omega⟩ = 2 := by native_decide
example : binaryNecklaceTable ⟨1, by omega⟩ = 3 := by native_decide
example : binaryNecklaceTable ⟨2, by omega⟩ = 4 := by native_decide
example : binaryNecklaceTable ⟨3, by omega⟩ = 6 := by native_decide
example : binaryNecklaceTable ⟨4, by omega⟩ = 8 := by native_decide
example : binaryNecklaceTable ⟨5, by omega⟩ = 14 := by native_decide

/-! ## 7. Lyndon words / aperiodic necklaces -/

/-- Mobius values needed for the divisor sums through length `6`. -/
def mobiusSmall : ℕ → ℤ
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => 0
  | 5 => -1
  | 6 => 1
  | _ => 0

/-- Numerator `Σ_{d|n} μ(n/d) * 2^d` in the binary Lyndon-word formula. -/
def lyndonNumerator (n : ℕ) : ℤ :=
  ((range (n + 1)).filter fun d => d ∣ n).sum
      (fun d => mobiusSmall (n / d) * (2 : ℤ) ^ d)

/-- Binary Lyndon words of length `n = 1..6`. -/
def lyndonWordsTable : Fin 6 → ℕ :=
  ![2, 1, 2, 3, 6, 9]

example :
    ∀ n : Fin 6, ((n.1 + 1) * lyndonWordsTable n : ℤ) = lyndonNumerator (n.1 + 1) := by
  native_decide

example : lyndonNumerator 1 = 2 := by native_decide
example : lyndonNumerator 2 = 2 := by native_decide
example : lyndonNumerator 3 = 6 := by native_decide
example : lyndonNumerator 4 = 12 := by native_decide
example : lyndonNumerator 5 = 30 := by native_decide
example : lyndonNumerator 6 = 54 := by native_decide

/-- Binary-necklace Burnside sample at length six. -/
theorem binaryNecklaceTable_six :
    binaryNecklaceTable ⟨5, by omega⟩ = 14 := by
  native_decide

/-- Binary Lyndon numerator sample at length six. -/
theorem lyndonNumerator_six :
    lyndonNumerator 6 = 54 := by
  native_decide



structure AutomataEnumerationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AutomataEnumerationBudgetCertificate.controlled
    (c : AutomataEnumerationBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AutomataEnumerationBudgetCertificate.budgetControlled
    (c : AutomataEnumerationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AutomataEnumerationBudgetCertificate.Ready
    (c : AutomataEnumerationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AutomataEnumerationBudgetCertificate.size
    (c : AutomataEnumerationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem automataEnumeration_budgetCertificate_le_size
    (c : AutomataEnumerationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAutomataEnumerationBudgetCertificate :
    AutomataEnumerationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAutomataEnumerationBudgetCertificate.Ready := by
  constructor
  · norm_num [AutomataEnumerationBudgetCertificate.controlled,
      sampleAutomataEnumerationBudgetCertificate]
  · norm_num [AutomataEnumerationBudgetCertificate.budgetControlled,
      sampleAutomataEnumerationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAutomataEnumerationBudgetCertificate.certificateBudgetWindow ≤
      sampleAutomataEnumerationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAutomataEnumerationBudgetCertificate.Ready := by
  constructor
  · norm_num [AutomataEnumerationBudgetCertificate.controlled,
      sampleAutomataEnumerationBudgetCertificate]
  · norm_num [AutomataEnumerationBudgetCertificate.budgetControlled,
      sampleAutomataEnumerationBudgetCertificate]

example :
    sampleAutomataEnumerationBudgetCertificate.certificateBudgetWindow ≤
      sampleAutomataEnumerationBudgetCertificate.size := by
  apply automataEnumeration_budgetCertificate_le_size
  constructor
  · norm_num [AutomataEnumerationBudgetCertificate.controlled,
      sampleAutomataEnumerationBudgetCertificate]
  · norm_num [AutomataEnumerationBudgetCertificate.budgetControlled,
      sampleAutomataEnumerationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AutomataEnumerationBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAutomataEnumerationBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAutomataEnumerationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.AutomataEnumeration
