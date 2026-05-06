/-
  Analytic Combinatorics — Part B
  Chapter IX — Large powers: saddle-point bounds and concentration.

  Flajolet & Sedgewick Chapter IX discusses the distribution of coefficients
  in large powers of generating functions.  The Gaussian approximation to
  binomial coefficients and concentration phenomena are verified here via
  finite numerical checks using native_decide.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset

namespace AnalyticCombinatorics.PartB.Ch9.LargePowers
/-! ## Section 1: Central binomial coefficient bounds (Gaussian peak) -/

/-- C(10,5) = 252. -/
example : Nat.choose 10 5 = 252 := by native_decide

/-- The central coefficient 252 is less than 1/4 of 2^10 = 1024. -/
example : 252 * 4 < 1024 := by native_decide

/-- The central coefficient 252 is more than 1/5 of 2^10 = 1024. -/
example : 252 * 5 > 1024 := by native_decide

/-- C(20,10) = 184756. -/
example : Nat.choose 20 10 = 184756 := by native_decide

/-! ## Section 2: Binomial tail bounds -/

/-- Sum of binomial coefficients from index `threshold` to `n`. -/
def binomialTail (n threshold : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n - threshold + 1), Nat.choose n (threshold + k)

/-- binomialTail 10 8 = C(10,8) + C(10,9) + C(10,10) = 45 + 10 + 1 = 56. -/
example : binomialTail 10 8 = 56 := by native_decide

/-- binomialTail 10 6 = C(10,6) + C(10,7) + C(10,8) + C(10,9) + C(10,10) = 386. -/
example : binomialTail 10 6 = 386 := by native_decide

/-! ## Section 3: Central mass (LLN illustration) -/

/-- Sum of binomial coefficients C(n, lo), C(n, lo+1), ..., C(n, hi). -/
def centralMass (n lo hi : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (hi - lo + 1), Nat.choose n (lo + k)

/-- The middle third of C(12, _) contains more than 75% of the total mass 2^12. -/
example : centralMass 12 4 8 > 3 * 2 ^ 12 / 4 := by native_decide

/-! ## Section 4: Binomial unimodality (center is maximum) -/

example : Nat.choose 10 3 ≤ Nat.choose 10 5 := by native_decide
example : Nat.choose 10 7 ≤ Nat.choose 10 5 := by native_decide
example : Nat.choose 12 4 ≤ Nat.choose 12 6 := by native_decide
example : Nat.choose 20 7 ≤ Nat.choose 20 10 := by native_decide
example : Nat.choose 20 13 ≤ Nat.choose 20 10 := by native_decide

/-! ## Section 5: Concentration inequality (crude) -/

/-- C(2n, n) * 2 < 4^n for n ≥ 2, illustrating that the peak is a vanishing
    fraction of the total. -/
example : Nat.choose 4 2 * 2 < 4 ^ 2 := by native_decide
example : Nat.choose 6 3 * 2 < 4 ^ 3 := by native_decide
example : Nat.choose 10 5 * 2 < 4 ^ 5 := by native_decide
example : Nat.choose 20 10 * 2 < 4 ^ 10 := by native_decide

/-- C(8,4) * 3 < 2^8: the peak term is less than 1/3 of the total,
    illustrating concentration away from the maximum. -/
example : Nat.choose 8 4 * 3 < 2 ^ 8 := by native_decide

/-- Central binomial peak in a large power. -/
def centralBinomialPeak (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n

theorem centralBinomialPeak_ten :
    centralBinomialPeak 10 = 184756 := by
  native_decide

/-- Cleared peak fraction against the full binomial mass. -/
def centralPeakSlack (n multiplier : ℕ) : ℕ :=
  2 ^ (2 * n) - multiplier * centralBinomialPeak n

theorem centralPeakSlack_four_three :
    centralPeakSlack 4 3 = 46 := by
  native_decide


structure LargePowersBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LargePowersBudgetCertificate.controlled
    (c : LargePowersBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LargePowersBudgetCertificate.budgetControlled
    (c : LargePowersBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LargePowersBudgetCertificate.Ready
    (c : LargePowersBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LargePowersBudgetCertificate.size
    (c : LargePowersBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem largePowers_budgetCertificate_le_size
    (c : LargePowersBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLargePowersBudgetCertificate :
    LargePowersBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLargePowersBudgetCertificate.Ready := by
  constructor
  · norm_num [LargePowersBudgetCertificate.controlled,
      sampleLargePowersBudgetCertificate]
  · norm_num [LargePowersBudgetCertificate.budgetControlled,
      sampleLargePowersBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLargePowersBudgetCertificate.certificateBudgetWindow ≤
      sampleLargePowersBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLargePowersBudgetCertificate.Ready := by
  constructor
  · norm_num [LargePowersBudgetCertificate.controlled,
      sampleLargePowersBudgetCertificate]
  · norm_num [LargePowersBudgetCertificate.budgetControlled,
      sampleLargePowersBudgetCertificate]

example :
    sampleLargePowersBudgetCertificate.certificateBudgetWindow ≤
      sampleLargePowersBudgetCertificate.size := by
  apply largePowers_budgetCertificate_le_size
  constructor
  · norm_num [LargePowersBudgetCertificate.controlled,
      sampleLargePowersBudgetCertificate]
  · norm_num [LargePowersBudgetCertificate.budgetControlled,
      sampleLargePowersBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LargePowersBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLargePowersBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLargePowersBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.LargePowers
