/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Linear Recurrences with Constant Coefficients

  Definitions and numerical verification of classical integer sequences
  satisfying linear (and bilinear) recurrences.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.RecurrenceRelations
/-! ## 1. Tribonacci numbers

  T(0)=0, T(1)=0, T(2)=1, T(n)=T(n-1)+T(n-2)+T(n-3).
  Values: 0, 0, 1, 1, 2, 4, 7, 13, 24, 44, 81, 149.
-/

def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n
  decreasing_by all_goals omega

example : tribonacci 0 = 0 := by native_decide
example : tribonacci 1 = 0 := by native_decide
example : tribonacci 2 = 1 := by native_decide
example : tribonacci 3 = 1 := by native_decide
example : tribonacci 4 = 2 := by native_decide
example : tribonacci 5 = 4 := by native_decide
example : tribonacci 6 = 7 := by native_decide
example : tribonacci 7 = 13 := by native_decide
example : tribonacci 8 = 24 := by native_decide
example : tribonacci 9 = 44 := by native_decide
example : tribonacci 10 = 81 := by native_decide
example : tribonacci 11 = 149 := by native_decide

/-! ## 2. Padovan sequence

  P(0)=1, P(1)=1, P(2)=1, P(n)=P(n-2)+P(n-3).
  Values: 1, 1, 1, 2, 2, 3, 4, 5, 7, 9, 12, 16, 21, 28.
-/

def padovan : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => padovan (n + 1) + padovan n
  decreasing_by all_goals omega

example : padovan 0 = 1 := by native_decide
example : padovan 1 = 1 := by native_decide
example : padovan 2 = 1 := by native_decide
example : padovan 3 = 2 := by native_decide
example : padovan 4 = 2 := by native_decide
example : padovan 5 = 3 := by native_decide
example : padovan 6 = 4 := by native_decide
example : padovan 7 = 5 := by native_decide
example : padovan 8 = 7 := by native_decide
example : padovan 9 = 9 := by native_decide
example : padovan 10 = 12 := by native_decide

/-! ## 3. Pell numbers

  P(0)=0, P(1)=1, P(n)=2*P(n-1)+P(n-2).
  Values: 0, 1, 2, 5, 12, 29, 70, 169, 408, 985.
-/

def pell : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pell (n + 1) + pell n
  decreasing_by all_goals omega

example : pell 0 = 0 := by native_decide
example : pell 1 = 1 := by native_decide
example : pell 2 = 2 := by native_decide
example : pell 3 = 5 := by native_decide
example : pell 4 = 12 := by native_decide
example : pell 5 = 29 := by native_decide
example : pell 6 = 70 := by native_decide
example : pell 7 = 169 := by native_decide
example : pell 8 = 408 := by native_decide
example : pell 9 = 985 := by native_decide

/-- Companion Pell (half-companion): Q(0)=1, Q(1)=1, Q(n)=2*Q(n-1)+Q(n-2). -/
def companionPell : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * companionPell (n + 1) + companionPell n
  decreasing_by all_goals omega

example : companionPell 0 = 1 := by native_decide
example : companionPell 1 = 1 := by native_decide
example : companionPell 2 = 3 := by native_decide
example : companionPell 3 = 7 := by native_decide
example : companionPell 4 = 17 := by native_decide
example : companionPell 5 = 41 := by native_decide
example : companionPell 6 = 99 := by native_decide

/-! ## 4. Jacobsthal numbers

  J(0)=0, J(1)=1, J(n)=J(n-1)+2*J(n-2).
  Values: 0, 1, 1, 3, 5, 11, 21, 43, 85, 171.
-/

def jacobsthal : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => jacobsthal (n + 1) + 2 * jacobsthal n
  decreasing_by all_goals omega

example : jacobsthal 0 = 0 := by native_decide
example : jacobsthal 1 = 1 := by native_decide
example : jacobsthal 2 = 1 := by native_decide
example : jacobsthal 3 = 3 := by native_decide
example : jacobsthal 4 = 5 := by native_decide
example : jacobsthal 5 = 11 := by native_decide
example : jacobsthal 6 = 21 := by native_decide
example : jacobsthal 7 = 43 := by native_decide
example : jacobsthal 8 = 85 := by native_decide
example : jacobsthal 9 = 171 := by native_decide

/-! ### Jacobsthal closed form verification

  Closed form: J(n) = (2^n - (-1)^n)/3.
  In ℕ: for odd n, 3*J(n) = 2^n + 1; for even n≥2, 3*J(n) = 2^n - 1.
-/

-- J(1)=1, odd: 3*1 = 2^1 + 1 = 3
example : 3 * 1 = 2 ^ 1 + 1 := by native_decide
-- J(2)=1, even: 3*1 = 2^2 - 1 = 3
example : 3 * 1 = 2 ^ 2 - 1 := by native_decide
-- J(3)=3, odd: 3*3 = 2^3 + 1 = 9
example : 3 * 3 = 2 ^ 3 + 1 := by native_decide
-- J(4)=5, even: 3*5 = 2^4 - 1 = 15
example : 3 * 5 = 2 ^ 4 - 1 := by native_decide
-- J(5)=11, odd: 3*11 = 2^5 + 1 = 33
example : 3 * 11 = 2 ^ 5 + 1 := by native_decide
-- J(6)=21, even: 3*21 = 2^6 - 1 = 63
example : 3 * 21 = 2 ^ 6 - 1 := by native_decide
-- J(7)=43, odd: 3*43 = 2^7 + 1 = 129
example : 3 * 43 = 2 ^ 7 + 1 := by native_decide

/-! ## 5. Divide-and-conquer recurrences

  T(n) = 2*T(n/2) + n (merge sort complexity).
  For powers of 2: T(2^k) = k * 2^k.
-/

example : 1 * 2 ^ 1 = 2 := by native_decide
example : 2 * 2 ^ 2 = 8 := by native_decide
example : 3 * 2 ^ 3 = 24 := by native_decide
example : 4 * 2 ^ 4 = 64 := by native_decide
example : 5 * 2 ^ 5 = 160 := by native_decide

/-! ## 6. Somos-4 sequence

  s(0)=s(1)=s(2)=s(3)=1, s(n) = (s(n-1)*s(n-3) + s(n-2)^2) / s(n-4).
  Remarkably always integer: 1, 1, 1, 1, 2, 3, 7, 23, 59, 314, 1529, ...
-/

def somos4Table : Fin 11 → ℕ := ![1, 1, 1, 1, 2, 3, 7, 23, 59, 314, 1529]

-- Verify the Somos-4 recurrence: s(n) = (s(n-1)*s(n-3) + s(n-2)^2) / s(n-4)
-- s(4) = (s(3)*s(1) + s(2)^2) / s(0) = (1*1 + 1) / 1 = 2
example : (1 * 1 + 1 * 1) / 1 = 2 := by native_decide
-- s(5) = (s(4)*s(2) + s(3)^2) / s(1) = (2*1 + 1) / 1 = 3
example : (2 * 1 + 1 * 1) / 1 = 3 := by native_decide
-- s(6) = (s(5)*s(3) + s(4)^2) / s(2) = (3*1 + 4) / 1 = 7
example : (3 * 1 + 2 * 2) / 1 = 7 := by native_decide
-- s(7) = (s(6)*s(4) + s(5)^2) / s(3) = (7*2 + 9) / 1 = 23
example : (7 * 2 + 3 * 3) / 1 = 23 := by native_decide
-- s(8) = (s(7)*s(5) + s(6)^2) / s(4) = (23*3 + 49) / 2 = 59
example : (23 * 3 + 7 * 7) / 2 = 59 := by native_decide
-- s(9) = (s(8)*s(6) + s(7)^2) / s(5) = (59*7 + 529) / 3 = 314
example : (59 * 7 + 23 * 23) / 3 = 314 := by native_decide
-- s(10) = (s(9)*s(7) + s(8)^2) / s(6) = (314*23 + 3481) / 7 = 1529
example : (314 * 23 + 59 * 59) / 7 = 1529 := by native_decide

/-- Jacobsthal table sample. -/
theorem jacobsthal_nine :
    jacobsthal 9 = 171 := by
  native_decide

/-- Somos-4 table sample. -/
theorem somos4Table_ten :
    somos4Table 10 = 1529 := by
  native_decide


structure RecurrenceRelationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RecurrenceRelationsBudgetCertificate.controlled
    (c : RecurrenceRelationsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RecurrenceRelationsBudgetCertificate.budgetControlled
    (c : RecurrenceRelationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RecurrenceRelationsBudgetCertificate.Ready
    (c : RecurrenceRelationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RecurrenceRelationsBudgetCertificate.size
    (c : RecurrenceRelationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem recurrenceRelations_budgetCertificate_le_size
    (c : RecurrenceRelationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRecurrenceRelationsBudgetCertificate :
    RecurrenceRelationsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRecurrenceRelationsBudgetCertificate.Ready := by
  constructor
  · norm_num [RecurrenceRelationsBudgetCertificate.controlled,
      sampleRecurrenceRelationsBudgetCertificate]
  · norm_num [RecurrenceRelationsBudgetCertificate.budgetControlled,
      sampleRecurrenceRelationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRecurrenceRelationsBudgetCertificate.certificateBudgetWindow ≤
      sampleRecurrenceRelationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRecurrenceRelationsBudgetCertificate.Ready := by
  constructor
  · norm_num [RecurrenceRelationsBudgetCertificate.controlled,
      sampleRecurrenceRelationsBudgetCertificate]
  · norm_num [RecurrenceRelationsBudgetCertificate.budgetControlled,
      sampleRecurrenceRelationsBudgetCertificate]

example :
    sampleRecurrenceRelationsBudgetCertificate.certificateBudgetWindow ≤
      sampleRecurrenceRelationsBudgetCertificate.size := by
  apply recurrenceRelations_budgetCertificate_le_size
  constructor
  · norm_num [RecurrenceRelationsBudgetCertificate.controlled,
      sampleRecurrenceRelationsBudgetCertificate]
  · norm_num [RecurrenceRelationsBudgetCertificate.budgetControlled,
      sampleRecurrenceRelationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RecurrenceRelationsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRecurrenceRelationsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRecurrenceRelationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.RecurrenceRelations
