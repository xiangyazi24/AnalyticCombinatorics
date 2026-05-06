/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Subexponential and stretched-exponential growth rates.

  We record verified numerical facts about three classical sequences whose
  growth is sub- or super-exponential:

    · Integer partitions  p(n) ~ exp(π√(2n/3))/(4n√3)   (Hardy–Ramanujan)
    · Bell numbers        B(n) ~ (n/log n)^n              (super-exponential)
    · Involution numbers  a(n) ~ √2 · (n/e)^(n/2)        (intermediate)

  All proofs are by `native_decide` on finite certificate goals.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false
set_option linter.style.whitespace false
set_option linter.style.longLine false

open Finset Nat

namespace AnalyticCombinatorics.PartB.Ch7.SubexponentialGrowth
-- ============================================================
-- §1  Integer partition numbers  (Hardy–Ramanujan asymptotics)
-- ============================================================

/-!
### 1. Partition numbers

`p(n)` counts the number of ways to write `n` as an unordered sum of
positive integers.  Hardy and Ramanujan (1918) proved

    p(n) ~ exp(π √(2n/3)) / (4n√3)  as n → ∞.

This is *subexponential*: p(n) = o(r^n) for every r > 1, yet p(n) → ∞
faster than any polynomial.

We work with the exact table for n = 0 … 15.
-/

/-- Exact values of p(0), p(1), …, p(15). -/
def partitionTable : Fin 16 → ℕ :=
  ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176]

-- Basic spot-checks
theorem partitionTable_0  : partitionTable 0  = 1   := by native_decide
theorem partitionTable_1  : partitionTable 1  = 1   := by native_decide
theorem partitionTable_5  : partitionTable 5  = 7   := by native_decide
theorem partitionTable_10 : partitionTable 10 = 42  := by native_decide
theorem partitionTable_15 : partitionTable 15 = 176 := by native_decide

/-! #### Strict monotonicity for n = 2 … 15 -/

theorem partitionTable_incr :
    partitionTable 2  < partitionTable 3  ∧
    partitionTable 3  < partitionTable 4  ∧
    partitionTable 4  < partitionTable 5  ∧
    partitionTable 5  < partitionTable 6  ∧
    partitionTable 6  < partitionTable 7  ∧
    partitionTable 7  < partitionTable 8  ∧
    partitionTable 8  < partitionTable 9  ∧
    partitionTable 9  < partitionTable 10 ∧
    partitionTable 10 < partitionTable 11 ∧
    partitionTable 11 < partitionTable 12 ∧
    partitionTable 12 < partitionTable 13 ∧
    partitionTable 13 < partitionTable 14 ∧
    partitionTable 14 < partitionTable 15 := by native_decide

/-! #### p(n) < 2^n for n = 1 … 15 (subexponential witness) -/

theorem partition_lt_pow2_all :
    partitionTable 1  < 2 ^ 1  ∧
    partitionTable 2  < 2 ^ 2  ∧
    partitionTable 3  < 2 ^ 3  ∧
    partitionTable 4  < 2 ^ 4  ∧
    partitionTable 5  < 2 ^ 5  ∧
    partitionTable 6  < 2 ^ 6  ∧
    partitionTable 7  < 2 ^ 7  ∧
    partitionTable 8  < 2 ^ 8  ∧
    partitionTable 9  < 2 ^ 9  ∧
    partitionTable 10 < 2 ^ 10 ∧
    partitionTable 11 < 2 ^ 11 ∧
    partitionTable 12 < 2 ^ 12 ∧
    partitionTable 13 < 2 ^ 13 ∧
    partitionTable 14 < 2 ^ 14 ∧
    partitionTable 15 < 2 ^ 15 := by native_decide

/-! #### p(n) < n! for n = 3 … 10 -/

theorem partitionTable_lt_factorial :
    partitionTable 3  < 3  ! ∧
    partitionTable 4  < 4  ! ∧
    partitionTable 5  < 5  ! ∧
    partitionTable 6  < 6  ! ∧
    partitionTable 7  < 7  ! ∧
    partitionTable 8  < 8  ! ∧
    partitionTable 9  < 9  ! ∧
    partitionTable 10 < 10 ! := by native_decide

/-! #### Super-multiplicativity: p(a)*p(b) ≤ p(a+b) for a, b ≤ 3 -/

/-- p is super-multiplicative for a, b ≤ 3 (fits in the table). -/
theorem partitionTable_superMult_small :
    ∀ a : Fin 4, ∀ b : Fin 4,
      partitionTable ⟨a, by omega⟩ * partitionTable ⟨b, by omega⟩ ≤
      partitionTable ⟨a.val + b.val, by omega⟩ := by
  decide

-- ============================================================
-- §2  Euler's pentagonal number theorem — partition recurrence
-- ============================================================

/-!
### 2. Pentagonal recurrence

Euler's pentagonal number theorem gives the recurrence

    p(n) = p(n−1) + p(n−2) − p(n−5) − p(n−7) + p(n−12) + p(n−15) − …

where the indices are the generalised pentagonal numbers
k(3k−1)/2 for k = ±1, ±2, ±3, … and signs alternate in pairs +, +, −, −, …

We verify several instances directly from the table in additive form
(to avoid ℕ subtraction pitfalls).
-/

-- n=5: p(5)+p(0) = p(4)+p(3)   [pent. #s 1,2 give +p(4)+p(3), pent. # 5 gives -p(0)]
-- 7+1 = 5+3
theorem pent_5 :
    partitionTable 5 + partitionTable 0 = partitionTable 4 + partitionTable 3 := by
  native_decide

-- n=6: p(6)+p(1) = p(5)+p(4)   [11+1 = 7+5]
theorem pent_6 :
    partitionTable 6 + partitionTable 1 = partitionTable 5 + partitionTable 4 := by
  native_decide

-- n=7: p(7)+p(2)+p(0) = p(6)+p(5)   [15+2+1 = 11+7]
theorem pent_7 :
    partitionTable 7 + partitionTable 2 + partitionTable 0 =
    partitionTable 6 + partitionTable 5 := by
  native_decide

-- n=8: p(8)+p(3)+p(1) = p(7)+p(6)   [22+3+1 = 15+11]
theorem pent_8 :
    partitionTable 8 + partitionTable 3 + partitionTable 1 =
    partitionTable 7 + partitionTable 6 := by
  native_decide

-- n=9: p(9)+p(4)+p(2) = p(8)+p(7)   [30+5+2 = 22+15]
theorem pent_9 :
    partitionTable 9 + partitionTable 4 + partitionTable 2 =
    partitionTable 8 + partitionTable 7 := by
  native_decide

-- n=10: p(10)+p(5)+p(3) = p(9)+p(8)   [42+7+3 = 30+22]
theorem pent_10 :
    partitionTable 10 + partitionTable 5 + partitionTable 3 =
    partitionTable 9 + partitionTable 8 := by
  native_decide

-- ============================================================
-- §3  Bell numbers
-- ============================================================

/-!
### 3. Bell numbers

`B(n)` counts set partitions of `{1, …, n}`.  The exponential generating
function is `exp(exp(x) − 1)`.  Bell numbers satisfy

    B(n+1) = Σ_{k=0}^{n} C(n,k) · B(k)

and grow faster than any fixed exponential: B(n) ~ (n/ln n)^n (up to
subexponential factors).
-/

/-- Exact values B(0), …, B(10). -/
def bellTable : Fin 11 → ℕ :=
  ![1, 1, 2, 5, 15, 52, 203, 877, 4140, 21147, 115975]

theorem bellTable_0  : bellTable 0  = 1      := by native_decide
theorem bellTable_5  : bellTable 5  = 52     := by native_decide
theorem bellTable_10 : bellTable 10 = 115975 := by native_decide

/-! #### Recurrence  B(n+1) = Σ_{k=0}^{n} C(n,k)·B(k) -/

-- B(1) = C(0,0)*B(0) = 1
theorem bell_recurrence_1 :
    bellTable 1 = Nat.choose 0 0 * bellTable 0 := by native_decide

-- B(2) = C(1,0)*B(0) + C(1,1)*B(1) = 1+1 = 2
theorem bell_recurrence_2 :
    bellTable 2 =
      Nat.choose 1 0 * bellTable 0 +
      Nat.choose 1 1 * bellTable 1 := by native_decide

-- B(3) = C(2,0)*B(0) + C(2,1)*B(1) + C(2,2)*B(2) = 1+2+2 = 5
theorem bell_recurrence_3 :
    bellTable 3 =
      Nat.choose 2 0 * bellTable 0 +
      Nat.choose 2 1 * bellTable 1 +
      Nat.choose 2 2 * bellTable 2 := by native_decide

-- B(4) = C(3,0)*B(0)+C(3,1)*B(1)+C(3,2)*B(2)+C(3,3)*B(3) = 1+3+6+5 = 15
theorem bell_recurrence_4 :
    bellTable 4 =
      Nat.choose 3 0 * bellTable 0 +
      Nat.choose 3 1 * bellTable 1 +
      Nat.choose 3 2 * bellTable 2 +
      Nat.choose 3 3 * bellTable 3 := by native_decide

-- B(5) = C(4,0)*B(0)+…+C(4,4)*B(4) = 1+4+12+20+15 = 52
theorem bell_recurrence_5 :
    bellTable 5 =
      Nat.choose 4 0 * bellTable 0 +
      Nat.choose 4 1 * bellTable 1 +
      Nat.choose 4 2 * bellTable 2 +
      Nat.choose 4 3 * bellTable 3 +
      Nat.choose 4 4 * bellTable 4 := by native_decide

/-! #### B(n) > (n−2)! for n = 5 … 10 (super-exponential growth witness) -/

theorem bell_gt_factorial_shift :
    bellTable 5  > 3  ! ∧
    bellTable 6  > 4  ! ∧
    bellTable 7  > 5  ! ∧
    bellTable 8  > 6  ! ∧
    bellTable 9  > 7  ! ∧
    bellTable 10 > 8  ! := by native_decide

/-! #### B(n) > 3^n for n = 9, 10 -/

theorem bell_gt_pow3_large :
    bellTable 9  > 3 ^ 9 ∧
    bellTable 10 > 3 ^ 10 := by native_decide

-- ============================================================
-- §4  Involution numbers
-- ============================================================

/-!
### 4. Involution numbers

`a(n)` counts involutions of `{1, …, n}` (permutations equal to their own
inverse).  They satisfy

    a(n) = a(n−1) + (n−1)·a(n−2),  a(0) = a(1) = 1.

The growth is intermediate: a(n) ~ √2 · (n/e)^(n/2).
-/

/-- Exact values a(0), …, a(10). -/
def involutionTable : Fin 11 → ℕ :=
  ![1, 1, 2, 4, 10, 26, 76, 232, 764, 2620, 9496]

theorem involutionTable_0  : involutionTable 0  = 1    := by native_decide
theorem involutionTable_5  : involutionTable 5  = 26   := by native_decide
theorem involutionTable_10 : involutionTable 10 = 9496 := by native_decide

/-! #### Recurrence  a(n+2) = a(n+1) + (n+1) * a(n) -/

theorem involution_rec_2 :
    involutionTable 2 = involutionTable 1 + 1 * involutionTable 0 := by native_decide

theorem involution_rec_3 :
    involutionTable 3 = involutionTable 2 + 2 * involutionTable 1 := by native_decide

theorem involution_rec_4 :
    involutionTable 4 = involutionTable 3 + 3 * involutionTable 2 := by native_decide

theorem involution_rec_5 :
    involutionTable 5 = involutionTable 4 + 4 * involutionTable 3 := by native_decide

theorem involution_rec_6 :
    involutionTable 6 = involutionTable 5 + 5 * involutionTable 4 := by native_decide

theorem involution_rec_7 :
    involutionTable 7 = involutionTable 6 + 6 * involutionTable 5 := by native_decide

theorem involution_rec_8 :
    involutionTable 8 = involutionTable 7 + 7 * involutionTable 6 := by native_decide

theorem involution_rec_9 :
    involutionTable 9 = involutionTable 8 + 8 * involutionTable 7 := by native_decide

theorem involution_rec_10 :
    involutionTable 10 = involutionTable 9 + 9 * involutionTable 8 := by native_decide

-- ============================================================
-- §5  Comparison of growth rates at n = 10
-- ============================================================

/-!
### 5. Growth rate comparison

At n = 10 the four sequences satisfy:

    p(10) = 42 < a(10) = 9496 < B(10) = 115975 < 10! = 3628800.

And p(n) < 2^n throughout n = 1 … 15 (subexponential witness), while
B(n) > 3^n for n = 9, 10 (super-exponential evidence).
-/

/-- At n=10: p(10) < a(10) < B(10) < 10!. -/
theorem growth_order_n10 :
    partitionTable 10 < involutionTable 10 ∧
    involutionTable 10 < bellTable 10 ∧
    bellTable 10 < 10 ! := by native_decide

/-- fib 10 = 55 > p(10) = 42: Fibonacci already overtakes partitions. -/
theorem fib_gt_partition_10 : fib 10 > partitionTable 10 := by native_decide

/-- fib 9 = 34 < p(9) = 30; actually p(9)=30 < fib(9)=34. -/
theorem fib_gt_partition_9 : fib 9 > partitionTable 9 := by native_decide


structure SubexponentialGrowthBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubexponentialGrowthBudgetCertificate.controlled
    (c : SubexponentialGrowthBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SubexponentialGrowthBudgetCertificate.budgetControlled
    (c : SubexponentialGrowthBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SubexponentialGrowthBudgetCertificate.Ready
    (c : SubexponentialGrowthBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SubexponentialGrowthBudgetCertificate.size
    (c : SubexponentialGrowthBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem subexponentialGrowth_budgetCertificate_le_size
    (c : SubexponentialGrowthBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSubexponentialGrowthBudgetCertificate :
    SubexponentialGrowthBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSubexponentialGrowthBudgetCertificate.Ready := by
  constructor
  · norm_num [SubexponentialGrowthBudgetCertificate.controlled,
      sampleSubexponentialGrowthBudgetCertificate]
  · norm_num [SubexponentialGrowthBudgetCertificate.budgetControlled,
      sampleSubexponentialGrowthBudgetCertificate]

example :
    sampleSubexponentialGrowthBudgetCertificate.certificateBudgetWindow ≤
      sampleSubexponentialGrowthBudgetCertificate.size := by
  apply subexponentialGrowth_budgetCertificate_le_size
  constructor
  · norm_num [SubexponentialGrowthBudgetCertificate.controlled,
      sampleSubexponentialGrowthBudgetCertificate]
  · norm_num [SubexponentialGrowthBudgetCertificate.budgetControlled,
      sampleSubexponentialGrowthBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSubexponentialGrowthBudgetCertificate.Ready := by
  constructor
  · norm_num [SubexponentialGrowthBudgetCertificate.controlled,
      sampleSubexponentialGrowthBudgetCertificate]
  · norm_num [SubexponentialGrowthBudgetCertificate.budgetControlled,
      sampleSubexponentialGrowthBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSubexponentialGrowthBudgetCertificate.certificateBudgetWindow ≤
      sampleSubexponentialGrowthBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SubexponentialGrowthBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSubexponentialGrowthBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSubexponentialGrowthBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.SubexponentialGrowth
