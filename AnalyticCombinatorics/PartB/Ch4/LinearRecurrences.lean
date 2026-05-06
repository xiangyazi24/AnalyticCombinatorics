/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Linear Recurrence Sequences and Their Properties

  Fibonacci, Lucas, Tribonacci, Padovan: definitions, value tables,
  and numerical identities following Flajolet & Sedgewick §IV.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.LinearRecurrences
/-! ## 1. Fibonacci numbers

  F(0)=0, F(1)=1, F(n+2)=F(n+1)+F(n).
  Values: 0,1,1,2,3,5,8,13,21,34,55,89,144,233,377,610.
-/

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n
  decreasing_by all_goals omega

/-! ### 1.1  Value table -/

example : fib 0 = 0 := by native_decide
example : fib 1 = 1 := by native_decide
example : fib 2 = 1 := by native_decide
example : fib 3 = 2 := by native_decide
example : fib 4 = 3 := by native_decide
example : fib 5 = 5 := by native_decide
example : fib 6 = 8 := by native_decide
example : fib 7 = 13 := by native_decide
example : fib 8 = 21 := by native_decide
example : fib 9 = 34 := by native_decide
example : fib 10 = 55 := by native_decide
example : fib 11 = 89 := by native_decide
example : fib 12 = 144 := by native_decide
example : fib 13 = 233 := by native_decide
example : fib 14 = 377 := by native_decide
example : fib 15 = 610 := by native_decide

/-! ### 1.2  Cassini identity  (in ℕ)

  The classical identity is F(n-1)·F(n+1) - F(n)² = (-1)ⁿ.
  In ℕ we split by parity:
    n even : F(n-1)·F(n+1) + 1 = F(n)² + 2  -- actually: F(n)² = F(n-1)·F(n+1) + 1
    n odd  : F(n)² + 1 = F(n-1)·F(n+1)

  We index "n-1,n,n+1" via k=0,1,… so that indices stay positive.
-/

-- n=2 (even): F(1)*F(3) = 1*2 = 2, F(2)^2 = 1; 2 = 1 + 1 ✓
example : fib 1 * fib 3 = fib 2 ^ 2 + 1 := by native_decide
-- n=3 (odd): F(2)*F(4) = 1*3 = 3, F(3)^2 = 4; 4 = 3 + 1 ✓
example : fib 3 ^ 2 = fib 2 * fib 4 + 1 := by native_decide
-- n=4 (even)
example : fib 3 * fib 5 = fib 4 ^ 2 + 1 := by native_decide
-- n=5 (odd)
example : fib 5 ^ 2 = fib 4 * fib 6 + 1 := by native_decide
-- n=6 (even)
example : fib 5 * fib 7 = fib 6 ^ 2 + 1 := by native_decide
-- n=7 (odd)
example : fib 7 ^ 2 = fib 6 * fib 8 + 1 := by native_decide
-- n=8 (even)
example : fib 7 * fib 9 = fib 8 ^ 2 + 1 := by native_decide

/-! ### 1.3  d'Ocagne identity  |F(m)·F(n+1) - F(m+1)·F(n)| = F(n-m) for specific pairs

  Classical identity: F(m)·F(n+1) - F(m+1)·F(n) = (-1)^(m+1)·F(n-m).
  In ℕ we pick cases where the difference is positive and equals F(n-m).
-/

-- (m,n)=(3,6), (-1)^4=+1: fib(3)*fib(7) - fib(4)*fib(6) = 2 = fib(3)
example : fib 3 * fib 7 - fib 4 * fib 6 = fib 3 := by native_decide
-- (m,n)=(5,8), (-1)^6=+1: fib(5)*fib(9) - fib(6)*fib(8) = 2 = fib(3) -- wait n-m=3
example : fib 5 * fib 9 - fib 6 * fib 8 = fib 3 := by native_decide
-- (m,n)=(5,9), (-1)^6=+1: fib(5)*fib(10) - fib(6)*fib(9) = fib(4)  (n-m=4)
example : fib 5 * fib 10 - fib 6 * fib 9 = fib 4 := by native_decide
-- Cassini as d'Ocagne with m=n-1 (odd n): F(n)^2 - F(n-1)*F(n+1) = 1
example : fib 5 * fib 5 - fib 4 * fib 6 = 1 := by native_decide

/-! ### 1.4  GCD property:  gcd(F(m), F(n)) = F(gcd(m,n)) for small cases -/

example : Nat.gcd (fib 6) (fib 9) = fib (Nat.gcd 6 9) := by native_decide
example : Nat.gcd (fib 4) (fib 6) = fib (Nat.gcd 4 6) := by native_decide
example : Nat.gcd (fib 5) (fib 10) = fib (Nat.gcd 5 10) := by native_decide
example : Nat.gcd (fib 8) (fib 12) = fib (Nat.gcd 8 12) := by native_decide
example : Nat.gcd (fib 6) (fib 10) = fib (Nat.gcd 6 10) := by native_decide

/-! ## 2. Lucas numbers

  L(0)=2, L(1)=1, L(n+2)=L(n+1)+L(n).
  Values: 2,1,3,4,7,11,18,29,47,76,123.
-/

def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n
  decreasing_by all_goals omega

/-! ### 2.1  Value table -/

example : lucas 0 = 2 := by native_decide
example : lucas 1 = 1 := by native_decide
example : lucas 2 = 3 := by native_decide
example : lucas 3 = 4 := by native_decide
example : lucas 4 = 7 := by native_decide
example : lucas 5 = 11 := by native_decide
example : lucas 6 = 18 := by native_decide
example : lucas 7 = 29 := by native_decide
example : lucas 8 = 47 := by native_decide
example : lucas 9 = 76 := by native_decide
example : lucas 10 = 123 := by native_decide

/-! ### 2.2  Relation: L(n) = F(n-1) + F(n+1) for n ≥ 1

  Equivalently for n ≥ 1:  lucas n = fib (n-1) + fib (n+1).
  We verify for n = 1..8 using shifted index k = n-1, i.e. lucas (k+1) = fib k + fib (k+2).
-/

example : lucas 1 = fib 0 + fib 2 := by native_decide
example : lucas 2 = fib 1 + fib 3 := by native_decide
example : lucas 3 = fib 2 + fib 4 := by native_decide
example : lucas 4 = fib 3 + fib 5 := by native_decide
example : lucas 5 = fib 4 + fib 6 := by native_decide
example : lucas 6 = fib 5 + fib 7 := by native_decide
example : lucas 7 = fib 6 + fib 8 := by native_decide
example : lucas 8 = fib 7 + fib 9 := by native_decide

/-! ### 2.3  Product identity: F(n)·L(n) = F(2n) for n = 1..6

  We compute F(2n) directly via fib.
-/

example : fib 1 * lucas 1 = fib 2 := by native_decide
example : fib 2 * lucas 2 = fib 4 := by native_decide
example : fib 3 * lucas 3 = fib 6 := by native_decide
example : fib 4 * lucas 4 = fib 8 := by native_decide
example : fib 5 * lucas 5 = fib 10 := by native_decide
example : fib 6 * lucas 6 = fib 12 := by native_decide

/-! ## 3. Tribonacci numbers

  T(0)=0, T(1)=0, T(2)=1, T(n+3)=T(n+2)+T(n+1)+T(n).
  Values: 0,0,1,1,2,4,7,13,24,44,81,149.
-/

def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n
  decreasing_by all_goals omega

/-! ### 3.1  Value table -/

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

/-! ### 3.2  Subexponential growth: T(n+1) < 2·T(n) for n ≥ 5

  The tribonacci constant ≈ 1.839 < 2, so eventually T(n+1)/T(n) < 2.
  Note T(5)=4=2*T(4) (equality at n=4), so strict inequality starts at n=5.
  We verify for n = 5..10.
-/

example : tribonacci 6 < 2 * tribonacci 5 := by native_decide
example : tribonacci 7 < 2 * tribonacci 6 := by native_decide
example : tribonacci 8 < 2 * tribonacci 7 := by native_decide
example : tribonacci 9 < 2 * tribonacci 8 := by native_decide
example : tribonacci 10 < 2 * tribonacci 9 := by native_decide
example : tribonacci 11 < 2 * tribonacci 10 := by native_decide

/-! ## 4. Padovan sequence

  P(0)=1, P(1)=1, P(2)=1, P(n+3)=P(n+1)+P(n).
  Values: 1,1,1,2,2,3,4,5,7,9,12,16,21.
-/

def padovan : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => padovan (n + 1) + padovan n
  decreasing_by all_goals omega

/-! ### 4.1  Value table -/

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
example : padovan 11 = 16 := by native_decide
example : padovan 12 = 21 := by native_decide

/-! ### 4.2  Subexponential growth: P(n+1) < 2·P(n) for n ≥ 3

  The plastic constant ≈ 1.324 < 2.
  Note P(3)=2=2*P(2) (equality at n=2), so strict inequality starts at n=3.
  We verify for n = 3..11.
-/

example : padovan 4 < 2 * padovan 3 := by native_decide
example : padovan 5 < 2 * padovan 4 := by native_decide
example : padovan 6 < 2 * padovan 5 := by native_decide
example : padovan 7 < 2 * padovan 6 := by native_decide
example : padovan 8 < 2 * padovan 7 := by native_decide
example : padovan 9 < 2 * padovan 8 := by native_decide
example : padovan 10 < 2 * padovan 9 := by native_decide
example : padovan 11 < 2 * padovan 10 := by native_decide
example : padovan 12 < 2 * padovan 11 := by native_decide

/-! ## 5. Exponential growth bounds

  The golden ratio φ = (1+√5)/2 ≈ 1.618 satisfies φ < 2, so F(n) < 2ⁿ.
  We verify F(n) < 2^n for n ≤ 15.
-/

example : fib 1 < 2 ^ 1 := by native_decide
example : fib 2 < 2 ^ 2 := by native_decide
example : fib 3 < 2 ^ 3 := by native_decide
example : fib 4 < 2 ^ 4 := by native_decide
example : fib 5 < 2 ^ 5 := by native_decide
example : fib 6 < 2 ^ 6 := by native_decide
example : fib 7 < 2 ^ 7 := by native_decide
example : fib 8 < 2 ^ 8 := by native_decide
example : fib 9 < 2 ^ 9 := by native_decide
example : fib 10 < 2 ^ 10 := by native_decide
example : fib 11 < 2 ^ 11 := by native_decide
example : fib 12 < 2 ^ 12 := by native_decide
example : fib 13 < 2 ^ 13 := by native_decide
example : fib 14 < 2 ^ 14 := by native_decide
example : fib 15 < 2 ^ 15 := by native_decide

-- Fibonacci grows superpolynomially: F(25) = 75025 > 50000
example : fib 25 > 50000 := by native_decide
-- F(30) = 832040 > 800000
example : fib 30 > 800000 := by native_decide

-- The Cassini relation F(n)^2 ≤ F(n-1)*F(n+1) + 1 (equality for even, + 1 for odd)
-- consolidates to: F(n)^2 ≤ F(n-1)*F(n+1) + 1 for all n ≥ 1
example : fib 2 ^ 2 ≤ fib 1 * fib 3 + 1 := by native_decide
example : fib 3 ^ 2 ≤ fib 2 * fib 4 + 1 := by native_decide
example : fib 4 ^ 2 ≤ fib 3 * fib 5 + 1 := by native_decide
example : fib 5 ^ 2 ≤ fib 4 * fib 6 + 1 := by native_decide
example : fib 6 ^ 2 ≤ fib 5 * fib 7 + 1 := by native_decide
example : fib 7 ^ 2 ≤ fib 6 * fib 8 + 1 := by native_decide
example : fib 8 ^ 2 ≤ fib 7 * fib 9 + 1 := by native_decide

/-! ## 6. Companion matrix / addition formula

  F(n+m) = F(n)·F(m+1) + F(n-1)·F(m).

  In ℕ with non-negative indices we write:
    fib (n + m) = fib n * fib (m + 1) + fib (n - 1) * fib m

  but ℕ subtraction at n=0 gives fib (0-1) = fib 0 = 0, which is consistent
  since fib 0 = 0.  We verify for concrete pairs.
-/

-- (n,m) = (3,4):  F(7) = F(3)*F(5) + F(2)*F(4) = 2*5 + 1*3 = 13 ✓
example : fib (3 + 4) = fib 3 * fib 5 + fib 2 * fib 4 := by native_decide
-- (n,m) = (5,3):  F(8) = F(5)*F(4) + F(4)*F(3) = 5*3 + 3*2 = 21 ✓
example : fib (5 + 3) = fib 5 * fib 4 + fib 4 * fib 3 := by native_decide
-- (n,m) = (4,4):  F(8) = F(4)*F(5) + F(3)*F(4) = 3*5 + 2*3 = 21 ✓
example : fib (4 + 4) = fib 4 * fib 5 + fib 3 * fib 4 := by native_decide

-- More general form fib(n+m) = fib(n)*fib(m+1) + fib(n-1)*fib(m) (n ≥ 1)
-- (n,m) = (3,4): fib(7) = fib(3)*fib(5) + fib(2)*fib(4)
example : fib 7 = fib 3 * fib 5 + fib 2 * fib 4 := by native_decide
-- (n,m) = (6,5): fib(11) = fib(6)*fib(6) + fib(5)*fib(5)
example : fib 11 = fib 6 * fib 6 + fib 5 * fib 5 := by native_decide
-- (n,m) = (5,5): fib(10) = fib(5)*fib(6) + fib(4)*fib(5)
example : fib 10 = fib 5 * fib 6 + fib 4 * fib 5 := by native_decide

/-- Fibonacci value sample used by the recurrence table. -/
theorem fib_fifteen :
    fib 15 = 610 := by
  native_decide

/-- Lucas value sample used by the recurrence table. -/
theorem lucas_ten :
    lucas 10 = 123 := by
  native_decide

/-- Tribonacci value sample used by the recurrence table. -/
theorem tribonacci_eleven :
    tribonacci 11 = 149 := by
  native_decide

/-- Padovan value sample used by the recurrence table. -/
theorem padovan_twelve :
    padovan 12 = 21 := by
  native_decide


structure LinearRecurrencesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LinearRecurrencesBudgetCertificate.controlled
    (c : LinearRecurrencesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LinearRecurrencesBudgetCertificate.budgetControlled
    (c : LinearRecurrencesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LinearRecurrencesBudgetCertificate.Ready
    (c : LinearRecurrencesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LinearRecurrencesBudgetCertificate.size
    (c : LinearRecurrencesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem linearRecurrences_budgetCertificate_le_size
    (c : LinearRecurrencesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLinearRecurrencesBudgetCertificate :
    LinearRecurrencesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleLinearRecurrencesBudgetCertificate.Ready := by
  constructor
  · norm_num [LinearRecurrencesBudgetCertificate.controlled,
      sampleLinearRecurrencesBudgetCertificate]
  · norm_num [LinearRecurrencesBudgetCertificate.budgetControlled,
      sampleLinearRecurrencesBudgetCertificate]

example :
    sampleLinearRecurrencesBudgetCertificate.certificateBudgetWindow ≤
      sampleLinearRecurrencesBudgetCertificate.size := by
  apply linearRecurrences_budgetCertificate_le_size
  constructor
  · norm_num [LinearRecurrencesBudgetCertificate.controlled,
      sampleLinearRecurrencesBudgetCertificate]
  · norm_num [LinearRecurrencesBudgetCertificate.budgetControlled,
      sampleLinearRecurrencesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLinearRecurrencesBudgetCertificate.Ready := by
  constructor
  · norm_num [LinearRecurrencesBudgetCertificate.controlled,
      sampleLinearRecurrencesBudgetCertificate]
  · norm_num [LinearRecurrencesBudgetCertificate.budgetControlled,
      sampleLinearRecurrencesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLinearRecurrencesBudgetCertificate.certificateBudgetWindow ≤
      sampleLinearRecurrencesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LinearRecurrencesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLinearRecurrencesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLinearRecurrencesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.LinearRecurrences
