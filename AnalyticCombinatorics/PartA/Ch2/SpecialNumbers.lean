import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.SpecialNumbers


open Finset

/-! ## Bernoulli numbers (rational) -/

/-- Compute Bernoulli numbers table up to index n. -/
def bernoulliTable : ℕ → Array ℚ
  | 0 => #[1]
  | n + 1 =>
    let prev := bernoulliTable n
    let s := ∑ k ∈ Finset.range (n + 1),
               (Nat.choose (n + 2) k : ℚ) * prev[k]!
    prev.push (- s / (n + 2 : ℚ))

/-- Bernoulli numbers via the standard recurrence. -/
def bernoulliNum (n : ℕ) : ℚ := (bernoulliTable n)[n]!

theorem bernoulliNum_zero : bernoulliNum 0 = 1 := by native_decide

theorem bernoulliNum_one : bernoulliNum 1 = -1/2 := by native_decide

theorem bernoulliNum_two : bernoulliNum 2 = 1/6 := by native_decide

theorem bernoulliNum_three : bernoulliNum 3 = 0 := by native_decide

theorem bernoulliNum_four : bernoulliNum 4 = -1/30 := by native_decide

/-! ## Narayana numbers -/

/-- Narayana number `N(n,k) = C(n,k) * C(n,k-1) / n`. -/
def narayana (n k : ℕ) : ℕ :=
  if n = 0 || k = 0 || k > n then 0
  else Nat.choose n k * Nat.choose n (k - 1) / n

theorem narayana_4_1 : narayana 4 1 = 1 := by native_decide

theorem narayana_4_2 : narayana 4 2 = 6 := by native_decide

theorem narayana_4_3 : narayana 4 3 = 6 := by native_decide

theorem narayana_4_4 : narayana 4 4 = 1 := by native_decide

/-- Catalan number (standard formula). -/
def catalan (n : ℕ) : ℕ :=
  if n = 0 then 1
  else Nat.choose (2 * n) n / (n + 1)

/-- Row sum of Narayana numbers equals the Catalan number. -/
theorem narayana_row_sum_1 :
    ∑ k ∈ Finset.range 1, narayana 1 (k + 1) = catalan 1 := by native_decide

theorem narayana_row_sum_2 :
    ∑ k ∈ Finset.range 2, narayana 2 (k + 1) = catalan 2 := by native_decide

theorem narayana_row_sum_3 :
    ∑ k ∈ Finset.range 3, narayana 3 (k + 1) = catalan 3 := by native_decide

theorem narayana_row_sum_4 :
    ∑ k ∈ Finset.range 4, narayana 4 (k + 1) = catalan 4 := by native_decide

theorem narayana_row_sum_5 :
    ∑ k ∈ Finset.range 5, narayana 5 (k + 1) = catalan 5 := by native_decide

theorem narayana_row_sum_6 :
    ∑ k ∈ Finset.range 6, narayana 6 (k + 1) = catalan 6 := by native_decide

/-! ## Lah numbers -/

/-- Lah number `L(n,k) = C(n-1, k-1) * n! / k!`. -/
def lahNumber (n k : ℕ) : ℕ :=
  if k = 0 then (if n = 0 then 1 else 0)
  else Nat.choose (n - 1) (k - 1) * Nat.factorial n / Nat.factorial k

theorem lahNumber_3_1 : lahNumber 3 1 = 6 := by native_decide

theorem lahNumber_3_2 : lahNumber 3 2 = 6 := by native_decide

theorem lahNumber_3_3 : lahNumber 3 3 = 1 := by native_decide

theorem lahNumber_4_1 : lahNumber 4 1 = 24 := by native_decide

theorem lahNumber_4_2 : lahNumber 4 2 = 36 := by native_decide

theorem lahNumber_4_3 : lahNumber 4 3 = 12 := by native_decide

theorem lahNumber_4_4 : lahNumber 4 4 = 1 := by native_decide

/-! ## Fibonacci identities -/

/-- Sum of first `n` Fibonacci numbers: fib(1) + ... + fib(n). -/
def fibSum (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, Nat.fib (k + 1)

theorem fibSum_1 : fibSum 1 = Nat.fib 3 - 1 := by native_decide

theorem fibSum_2 : fibSum 2 = Nat.fib 4 - 1 := by native_decide

theorem fibSum_3 : fibSum 3 = Nat.fib 5 - 1 := by native_decide

theorem fibSum_4 : fibSum 4 = Nat.fib 6 - 1 := by native_decide

theorem fibSum_5 : fibSum 5 = Nat.fib 7 - 1 := by native_decide

theorem fibSum_6 : fibSum 6 = Nat.fib 8 - 1 := by native_decide

theorem fibSum_7 : fibSum 7 = Nat.fib 9 - 1 := by native_decide

theorem fibSum_8 : fibSum 8 = Nat.fib 10 - 1 := by native_decide

theorem fibSum_9 : fibSum 9 = Nat.fib 11 - 1 := by native_decide

theorem fibSum_10 : fibSum 10 = Nat.fib 12 - 1 := by native_decide

/-- Cassini's identity LHS: fib(n+2)*fib(n) - fib(n+1)^2. -/
def cassiniLHS (n : ℕ) : ℤ :=
  (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2

theorem cassini_0 : cassiniLHS 0 = (-1)^(0+1) := by native_decide

theorem cassini_1 : cassiniLHS 1 = (-1)^(1+1) := by native_decide

theorem cassini_2 : cassiniLHS 2 = (-1)^(2+1) := by native_decide

theorem cassini_3 : cassiniLHS 3 = (-1)^(3+1) := by native_decide

theorem cassini_4 : cassiniLHS 4 = (-1)^(4+1) := by native_decide

theorem cassini_5 : cassiniLHS 5 = (-1)^(5+1) := by native_decide

theorem cassini_6 : cassiniLHS 6 = (-1)^(6+1) := by native_decide

theorem cassini_7 : cassiniLHS 7 = (-1)^(7+1) := by native_decide

theorem cassini_8 : cassiniLHS 8 = (-1)^(8+1) := by native_decide

theorem cassini_9 : cassiniLHS 9 = (-1)^(9+1) := by native_decide

theorem cassini_10 : cassiniLHS 10 = (-1)^(10+1) := by native_decide

theorem cassini_11 : cassiniLHS 11 = (-1)^(11+1) := by native_decide

theorem cassini_12 : cassiniLHS 12 = (-1)^(12+1) := by native_decide

/-! ## Catalan convolution (Segner recurrence) -/

/-- Compute Catalan numbers table via Segner recurrence up to index n. -/
def catalanTable : ℕ → Array ℕ
  | 0 => #[1]
  | n + 1 =>
    let prev := catalanTable n
    let val := ∑ k ∈ Finset.range (n + 1), prev[k]! * prev[n - k]!
    prev.push val

/-- Catalan numbers via the Segner convolution recurrence. -/
def catalanConv (n : ℕ) : ℕ := (catalanTable n)[n]!

theorem catalanConv_eq_catalan_0 :
    catalanConv 0 = Nat.choose (2*0) 0 / (0+1) := by native_decide

theorem catalanConv_eq_catalan_1 :
    catalanConv 1 = Nat.choose (2*1) 1 / (1+1) := by native_decide

theorem catalanConv_eq_catalan_2 :
    catalanConv 2 = Nat.choose (2*2) 2 / (2+1) := by native_decide

theorem catalanConv_eq_catalan_3 :
    catalanConv 3 = Nat.choose (2*3) 3 / (3+1) := by native_decide

theorem catalanConv_eq_catalan_4 :
    catalanConv 4 = Nat.choose (2*4) 4 / (4+1) := by native_decide

theorem catalanConv_eq_catalan_5 :
    catalanConv 5 = Nat.choose (2*5) 5 / (5+1) := by native_decide

theorem catalanConv_eq_catalan_6 :
    catalanConv 6 = Nat.choose (2*6) 6 / (6+1) := by native_decide

theorem catalanConv_eq_catalan_7 :
    catalanConv 7 = Nat.choose (2*7) 7 / (7+1) := by native_decide

theorem catalanConv_eq_catalan_8 :
    catalanConv 8 = Nat.choose (2*8) 8 / (8+1) := by native_decide



structure SpecialNumbersBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SpecialNumbersBudgetCertificate.controlled
    (c : SpecialNumbersBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SpecialNumbersBudgetCertificate.budgetControlled
    (c : SpecialNumbersBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SpecialNumbersBudgetCertificate.Ready
    (c : SpecialNumbersBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SpecialNumbersBudgetCertificate.size
    (c : SpecialNumbersBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem specialNumbers_budgetCertificate_le_size
    (c : SpecialNumbersBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSpecialNumbersBudgetCertificate :
    SpecialNumbersBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSpecialNumbersBudgetCertificate.Ready := by
  constructor
  · norm_num [SpecialNumbersBudgetCertificate.controlled,
      sampleSpecialNumbersBudgetCertificate]
  · norm_num [SpecialNumbersBudgetCertificate.budgetControlled,
      sampleSpecialNumbersBudgetCertificate]

example :
    sampleSpecialNumbersBudgetCertificate.certificateBudgetWindow ≤
      sampleSpecialNumbersBudgetCertificate.size := by
  apply specialNumbers_budgetCertificate_le_size
  constructor
  · norm_num [SpecialNumbersBudgetCertificate.controlled,
      sampleSpecialNumbersBudgetCertificate]
  · norm_num [SpecialNumbersBudgetCertificate.budgetControlled,
      sampleSpecialNumbersBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSpecialNumbersBudgetCertificate.Ready := by
  constructor
  · norm_num [SpecialNumbersBudgetCertificate.controlled,
      sampleSpecialNumbersBudgetCertificate]
  · norm_num [SpecialNumbersBudgetCertificate.budgetControlled,
      sampleSpecialNumbersBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSpecialNumbersBudgetCertificate.certificateBudgetWindow ≤
      sampleSpecialNumbersBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SpecialNumbersBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSpecialNumbersBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSpecialNumbersBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.SpecialNumbers
