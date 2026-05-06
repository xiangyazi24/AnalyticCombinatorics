/-
  Chapter I — Necklaces and Burnside's lemma.

  A `k`-colored necklace of length `n` is a word modulo cyclic rotation.  The
  count is represented by the standard Burnside divisor sum, with natural-number
  division used for the final quotient.
-/
import Mathlib.Tactic

set_option linter.style.show false
set_option linter.style.nativeDecide false

open Finset

namespace AnalyticCombinatorics.PartA.Ch1.Necklaces
/-- Burnside numerator for `k`-colored necklaces of length `n`. -/
def necklaceBurnsideSum (k n : ℕ) : ℕ :=
  ∑ d ∈ Nat.divisors n, Nat.totient d * k ^ (n / d)

/-- Number of `k`-colored necklaces with `n` beads.

The empty necklace is counted once.  For positive `n`, this is

`(∑ d ∈ Nat.divisors n, Nat.totient d * k ^ (n / d)) / n`.
-/
def necklaceCount (k n : ℕ) : ℕ :=
  if n = 0 then 1 else necklaceBurnsideSum k n / n

/-- Number of binary necklaces with `n` beads. -/
def binaryNecklaceCount (n : ℕ) : ℕ :=
  necklaceCount 2 n

example : necklaceCount 2 0 = 1 := by native_decide

example : necklaceCount 2 1 = 2 := by native_decide
example : necklaceCount 2 2 = 3 := by native_decide
example : necklaceCount 2 3 = 4 := by native_decide
example : necklaceCount 2 4 = 6 := by native_decide
example : necklaceCount 2 5 = 8 := by native_decide
example : necklaceCount 2 6 = 14 := by native_decide

example : binaryNecklaceCount 1 = 2 := by native_decide
example : binaryNecklaceCount 2 = 3 := by native_decide
example : binaryNecklaceCount 3 = 4 := by native_decide
example : binaryNecklaceCount 4 = 6 := by native_decide
example : binaryNecklaceCount 5 = 8 := by native_decide
example : binaryNecklaceCount 6 = 14 := by native_decide

example : necklaceCount 3 1 = 3 := by native_decide
example : necklaceCount 3 2 = 6 := by native_decide
example : necklaceCount 3 3 = 11 := by native_decide
example : necklaceCount 3 4 = 24 := by native_decide

example :
    1 * necklaceCount 2 1 =
      ∑ d ∈ Nat.divisors 1, Nat.totient d * 2 ^ (1 / d) := by
  native_decide

example :
    2 * necklaceCount 2 2 =
      ∑ d ∈ Nat.divisors 2, Nat.totient d * 2 ^ (2 / d) := by
  native_decide

example :
    3 * necklaceCount 2 3 =
      ∑ d ∈ Nat.divisors 3, Nat.totient d * 2 ^ (3 / d) := by
  native_decide

example :
    4 * necklaceCount 2 4 =
      ∑ d ∈ Nat.divisors 4, Nat.totient d * 2 ^ (4 / d) := by
  native_decide

example :
    5 * necklaceCount 2 5 =
      ∑ d ∈ Nat.divisors 5, Nat.totient d * 2 ^ (5 / d) := by
  native_decide

example :
    6 * necklaceCount 2 6 =
      ∑ d ∈ Nat.divisors 6, Nat.totient d * 2 ^ (6 / d) := by
  native_decide

example :
    7 * necklaceCount 2 7 =
      ∑ d ∈ Nat.divisors 7, Nat.totient d * 2 ^ (7 / d) := by
  native_decide

example :
    8 * necklaceCount 2 8 =
      ∑ d ∈ Nat.divisors 8, Nat.totient d * 2 ^ (8 / d) := by
  native_decide

/-- Binary necklace count at length six. -/
theorem binaryNecklaceCount_six :
    binaryNecklaceCount 6 = 14 := by
  native_decide

/-- Ternary necklace count at length four. -/
theorem ternaryNecklaceCount_four :
    necklaceCount 3 4 = 24 := by
  native_decide

/-- Burnside numerator recovers the quotient after multiplying by length. -/
theorem necklaceBurnside_binary_eight :
    8 * necklaceCount 2 8 = necklaceBurnsideSum 2 8 := by
  native_decide


structure NecklacesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def NecklacesBudgetCertificate.controlled
    (c : NecklacesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def NecklacesBudgetCertificate.budgetControlled
    (c : NecklacesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def NecklacesBudgetCertificate.Ready
    (c : NecklacesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def NecklacesBudgetCertificate.size
    (c : NecklacesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem necklaces_budgetCertificate_le_size
    (c : NecklacesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleNecklacesBudgetCertificate :
    NecklacesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleNecklacesBudgetCertificate.Ready := by
  constructor
  · norm_num [NecklacesBudgetCertificate.controlled,
      sampleNecklacesBudgetCertificate]
  · norm_num [NecklacesBudgetCertificate.budgetControlled,
      sampleNecklacesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleNecklacesBudgetCertificate.certificateBudgetWindow ≤
      sampleNecklacesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleNecklacesBudgetCertificate.Ready := by
  constructor
  · norm_num [NecklacesBudgetCertificate.controlled,
      sampleNecklacesBudgetCertificate]
  · norm_num [NecklacesBudgetCertificate.budgetControlled,
      sampleNecklacesBudgetCertificate]

example :
    sampleNecklacesBudgetCertificate.certificateBudgetWindow ≤
      sampleNecklacesBudgetCertificate.size := by
  apply necklaces_budgetCertificate_le_size
  constructor
  · norm_num [NecklacesBudgetCertificate.controlled,
      sampleNecklacesBudgetCertificate]
  · norm_num [NecklacesBudgetCertificate.budgetControlled,
      sampleNecklacesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List NecklacesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleNecklacesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleNecklacesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.Necklaces
