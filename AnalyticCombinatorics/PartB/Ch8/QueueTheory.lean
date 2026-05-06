/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VIII/IX — Queueing and allocation models with saddle-point asymptotics.

  This file verifies combinatorial identities for lattice path models,
  ballot problems, stack-sortable permutations, M/M/1 queue statistics,
  and the Lindström–Gessel–Viennot lemma via native numerical checks.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch8.QueueTheory
/-! ## 1. Catalan ballot sequences (queue paths)

  The number of paths from (0,0) to (2n,0) that stay ≥ 0 with steps +1/−1
  equals the n-th Catalan number C(n) = C(2n,n)/(n+1).
-/

/-- Catalan numbers C(0)..C(7) as a lookup table. -/
def catalanQueue : Fin 8 → ℕ := ![1, 1, 2, 5, 14, 42, 132, 429]

example : catalanQueue 0 = 1 := by native_decide
example : catalanQueue 1 = 1 := by native_decide
example : catalanQueue 2 = 2 := by native_decide
example : catalanQueue 3 = 5 := by native_decide
example : catalanQueue 4 = 14 := by native_decide
example : catalanQueue 5 = 42 := by native_decide
example : catalanQueue 6 = 132 := by native_decide
example : catalanQueue 7 = 429 := by native_decide

/-! ## 2. Ballot problem (strict)

  In an election with scores a > b, the probability that candidate A is
  strictly ahead throughout the count is (a−b)/(a+b).
  The number of such sequences is (a−b)/(a+b) · C(a+b, a).
-/

-- a=4, b=3: (4-3)/(4+3) * C(7,4) = 1/7 * 35 = 5
example : 1 * Nat.choose 7 4 / 7 = 5 := by native_decide

-- a=5, b=3: (5-3)/(5+3) * C(8,5) = 2/8 * 56 = 14
example : 2 * Nat.choose 8 5 / 8 = 14 := by native_decide

-- a=6, b=4: (6-4)/(6+4) * C(10,6) = 2/10 * 210 = 42 = C(5)
example : 2 * Nat.choose 10 6 / 10 = 42 := by native_decide

/-! ## 3. Stack-sortable permutations

  The number of permutations of n elements sortable by a single stack
  (those avoiding the 231 pattern) equals C(n) = C(2n,n)/(n+1).
-/

-- n=4: C(8,4)/5 = 70/5 = 14
example : Nat.choose 8 4 / 5 = 14 := by native_decide

-- n=5: C(10,5)/6 = 252/6 = 42
example : Nat.choose 10 5 / 6 = 42 := by native_decide

-- n=6: C(12,6)/7 = 924/7 = 132
example : Nat.choose 12 6 / 7 = 132 := by native_decide

/-! ## 4. Random walks — Narayana numbers

  Narayana number N(n,k) = (1/n) · C(n,k) · C(n,k−1) counts Dyck paths
  of semilength n with exactly k peaks.
  Row sums satisfy Σ_{k=1}^n N(n,k) = C(n).
-/

/-- Narayana number N(n,k). -/
def narayana (n k : ℕ) : ℕ :=
  if n = 0 ∨ k = 0 ∨ k > n then 0
  else Nat.choose n k * Nat.choose n (k - 1) / n

-- Verify individual values for n=5
example : narayana 5 1 = 1 := by native_decide
example : narayana 5 2 = 10 := by native_decide
example : narayana 5 3 = 20 := by native_decide
example : narayana 5 4 = 10 := by native_decide
example : narayana 5 5 = 1 := by native_decide

-- Row sum N(5,1)+N(5,2)+N(5,3)+N(5,4)+N(5,5) = 42 = C(5)
example : narayana 5 1 + narayana 5 2 + narayana 5 3 +
          narayana 5 4 + narayana 5 5 = 42 := by native_decide

-- Row sum for n=4: N(4,1)+N(4,2)+N(4,3)+N(4,4) = 14 = C(4)
example : narayana 4 1 + narayana 4 2 + narayana 4 3 +
          narayana 4 4 = 14 := by native_decide

/-! ## 5. M/M/1 queue statistics

  In an M/M/1 queue with traffic intensity ρ < 1:
  • Expected number of customers: E[L] = ρ/(1−ρ)
  • Variance: Var[L] = ρ/(1−ρ)²
-/

-- E[L] at ρ = 1/2: (1/2)/(1/2) = 1
example : (1 : ℚ) / 2 / (1 - 1 / 2) = 1 := by native_decide

-- E[L] at ρ = 3/4: (3/4)/(1/4) = 3
example : (3 : ℚ) / 4 / (1 - 3 / 4) = 3 := by native_decide

-- Var[L] at ρ = 1/2: (1/2)/(1/2)² = (1/2)/(1/4) = 2
example : (1 : ℚ) / 2 / ((1 / 2) ^ 2) = 2 := by native_decide

-- Var[L] at ρ = 2/3: (2/3)/(1/3)² = (2/3)/(1/9) = 6
example : (2 : ℚ) / 3 / ((1 / 3) ^ 2) = 6 := by native_decide

/-! ## 6. Lattice path model (Lindström–Gessel–Viennot)

  The LGV lemma: the number of non-intersecting lattice path families
  is given by a determinant of individual path counts.
  We verify specific 2×2 determinant identities from binomial matrices.
-/

-- det [[C(4,1), C(4,2)], [C(5,1), C(5,2)]] = 4·10 − 6·5 = 10
example : 4 * 10 - 6 * 5 = 10 := by native_decide

-- Equivalently using Nat.choose
example : Nat.choose 4 1 * Nat.choose 5 2 - Nat.choose 4 2 * Nat.choose 5 1 = 10 := by
  native_decide

-- det [[C(5,2), C(5,3)], [C(6,2), C(6,3)]] = 10·20 − 10·15 = 50
example : Nat.choose 5 2 * Nat.choose 6 3 - Nat.choose 5 3 * Nat.choose 6 2 = 50 := by
  native_decide

-- det [[C(6,2), C(6,3)], [C(7,2), C(7,3)]] = 15·35 − 20·21 = 525 − 420 = 105
example : Nat.choose 6 2 * Nat.choose 7 3 - Nat.choose 6 3 * Nat.choose 7 2 = 105 := by
  native_decide

/-- Strict ballot count with natural-number division. -/
def strictBallotCount (a b : ℕ) : ℕ :=
  (a - b) * Nat.choose (a + b) a / (a + b)

theorem strictBallotCount_6_4 :
    strictBallotCount 6 4 = 42 := by
  native_decide

/-- Queue length mean for an M/M/1 queue at rational traffic intensity. -/
def mmOneMean (rho : ℚ) : ℚ :=
  rho / (1 - rho)

theorem mmOneMean_three_quarters :
    mmOneMean (3 / 4) = 3 := by
  native_decide


structure QueueTheoryBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QueueTheoryBudgetCertificate.controlled
    (c : QueueTheoryBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def QueueTheoryBudgetCertificate.budgetControlled
    (c : QueueTheoryBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def QueueTheoryBudgetCertificate.Ready
    (c : QueueTheoryBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def QueueTheoryBudgetCertificate.size
    (c : QueueTheoryBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem queueTheory_budgetCertificate_le_size
    (c : QueueTheoryBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleQueueTheoryBudgetCertificate :
    QueueTheoryBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleQueueTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [QueueTheoryBudgetCertificate.controlled,
      sampleQueueTheoryBudgetCertificate]
  · norm_num [QueueTheoryBudgetCertificate.budgetControlled,
      sampleQueueTheoryBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleQueueTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleQueueTheoryBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleQueueTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [QueueTheoryBudgetCertificate.controlled,
      sampleQueueTheoryBudgetCertificate]
  · norm_num [QueueTheoryBudgetCertificate.budgetControlled,
      sampleQueueTheoryBudgetCertificate]

example :
    sampleQueueTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleQueueTheoryBudgetCertificate.size := by
  apply queueTheory_budgetCertificate_le_size
  constructor
  · norm_num [QueueTheoryBudgetCertificate.controlled,
      sampleQueueTheoryBudgetCertificate]
  · norm_num [QueueTheoryBudgetCertificate.budgetControlled,
      sampleQueueTheoryBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List QueueTheoryBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleQueueTheoryBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleQueueTheoryBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.QueueTheory
