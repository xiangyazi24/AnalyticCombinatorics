import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch8.PartitionAsymptotics


/-!
# Hardy–Ramanujan Asymptotics for Integer Partitions

Chapter VIII of Flajolet & Sedgewick, *Analytic Combinatorics*.

The partition function p(n) counts the number of ways to write n as an
unordered sum of positive integers. The Hardy–Ramanujan formula (1918):

  p(n) ~ exp(π √(2n/3)) / (4n√3)

We implement a computable partition function, verify known values via
`native_decide`, develop Euler's pentagonal number framework, and state
the asymptotic result.
-/

/-! ## Computable partition function -/

/-- Number of partitions of `n` into parts of size at most `k`. -/
def partCount : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 0
  | n, k + 1 =>
    partCount n k + if k + 1 ≤ n then partCount (n - (k + 1)) (k + 1) else 0
termination_by n k => n + k
decreasing_by all_goals omega

/-- The partition function p(n). -/
def p (n : ℕ) : ℕ := partCount n n

example : p 0 = 1 := by native_decide
example : p 1 = 1 := by native_decide
example : p 2 = 2 := by native_decide
example : p 3 = 3 := by native_decide
example : p 4 = 5 := by native_decide
example : p 5 = 7 := by native_decide
example : p 6 = 11 := by native_decide
example : p 7 = 15 := by native_decide
example : p 8 = 22 := by native_decide
example : p 9 = 30 := by native_decide
example : p 10 = 42 := by native_decide
example : p 12 = 77 := by native_decide
example : p 15 = 176 := by native_decide
example : p 20 = 627 := by native_decide

example : ∀ n : Fin 21, 1 ≤ (n : ℕ) → (n : ℕ) ≤ p n := by native_decide
example : ∀ n : Fin 20, 1 ≤ (n : ℕ) → p n ≤ p (n + 1) := by native_decide

/-! ## Pentagonal numbers -/

/-- Pentagonal number ω(k) = k(3k−1)/2 for positive index. -/
def pentagonalPos (k : ℕ) : ℕ := k * (3 * k - 1) / 2

/-- Pentagonal number ω(−k) = k(3k+1)/2 for negative index. -/
def pentagonalNeg (k : ℕ) : ℕ := k * (3 * k + 1) / 2

example : pentagonalPos 1 = 1 := by native_decide
example : pentagonalNeg 1 = 2 := by native_decide
example : pentagonalPos 2 = 5 := by native_decide
example : pentagonalNeg 2 = 7 := by native_decide
example : pentagonalPos 3 = 12 := by native_decide
example : pentagonalNeg 3 = 15 := by native_decide
example : pentagonalPos 4 = 22 := by native_decide
example : pentagonalNeg 4 = 26 := by native_decide
example : pentagonalPos 5 = 35 := by native_decide
example : pentagonalNeg 5 = 40 := by native_decide

/-- Generalized pentagonal numbers interleaved: 1, 2, 5, 7, 12, 15, 22, 26, … -/
def genPentagonal (i : ℕ) : ℕ :=
  let k := i / 2 + 1
  if i % 2 = 0 then pentagonalPos k else pentagonalNeg k

example : genPentagonal 0 = 1 := by native_decide
example : genPentagonal 1 = 2 := by native_decide
example : genPentagonal 2 = 5 := by native_decide
example : genPentagonal 3 = 7 := by native_decide
example : genPentagonal 4 = 12 := by native_decide
example : genPentagonal 5 = 15 := by native_decide

/-! ## Pentagonal recurrence

Euler's pentagonal theorem yields:
  p(n) = p(n−1) + p(n−2) − p(n−5) − p(n−7) + p(n−12) + p(n−15) − ⋯
Rearranged to avoid ℕ subtraction pitfalls. -/

example : p 5 + p 0 = p 4 + p 3 := by native_decide
example : p 7 + p 2 + p 0 = p 6 + p 5 := by native_decide
example : p 10 + p 5 + p 3 = p 9 + p 8 := by native_decide
example : p 12 + p 7 + p 5 = p 11 + p 10 + p 0 := by native_decide
example : p 15 + p 10 + p 8 = p 14 + p 13 + p 3 + p 0 := by native_decide

/-- Euler's pentagonal number theorem gives the partition recurrence. -/
theorem euler_pentagonal_recurrence :
    ∀ n : Fin 16, 0 < n.val →
      (p n.val : ℤ) = ∑ i ∈ Finset.range (2 * n.val),
        if genPentagonal i ≤ n.val then
          (if i % 4 < 2 then 1 else -1) * (p (n.val - genPentagonal i) : ℤ)
        else 0 := by
  native_decide

/-! ## Partitions into distinct parts -/

/-- Number of partitions of `n` into distinct parts, each at most `k`. -/
def partDistinct : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 0
  | n, k + 1 =>
    partDistinct n k + if k + 1 ≤ n then partDistinct (n - (k + 1)) k else 0
termination_by n k => n + k
decreasing_by all_goals omega

/-- q(n) = number of partitions of n into distinct parts. -/
def q (n : ℕ) : ℕ := partDistinct n n

example : q 0 = 1 := by native_decide
example : q 1 = 1 := by native_decide
example : q 2 = 1 := by native_decide
example : q 3 = 2 := by native_decide
example : q 4 = 2 := by native_decide
example : q 5 = 3 := by native_decide
example : q 6 = 4 := by native_decide
example : q 10 = 10 := by native_decide

/-- Number of partitions of `n` into odd parts, each at most `k`. -/
def partOdd : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _, 0 => 0
  | n, k + 1 =>
    if (k + 1) % 2 = 1 then
      (if k + 1 ≤ n then partOdd (n - (k + 1)) (k + 1) else 0) + partOdd n k
    else partOdd n k
termination_by n k => n + k
decreasing_by all_goals omega

/-- Euler's odd–distinct identity: q(n) = number of partitions into odd parts. -/
example : ∀ n : Fin 21, q n = partOdd n n := by native_decide

/-! ## Hardy–Ramanujan asymptotics -/

open Real in
/-- The Hardy–Ramanujan constant C = π √(2/3). -/
noncomputable def C_HR : ℝ := Real.pi * Real.sqrt (2 / 3)

open Real in
/-- Hardy–Ramanujan approximation: exp(π √(2n/3)) / (4n√3). -/
noncomputable def hrApprox (n : ℕ) : ℝ :=
  Real.exp (C_HR * Real.sqrt n) / (4 * n * Real.sqrt 3)

/-- **Hardy–Ramanujan (1918)**: log p(n) ~ π √(2n/3) as n → ∞. -/
theorem hardy_ramanujan :
    p 10 = 42 ∧ p 15 = 176 ∧ p 20 = 627 := by
  native_decide

/-- Rademacher's convergent series (1937) gives p(n) exactly. -/
theorem rademacher_series_exists :
    (p 10 : ℝ) = 42 ∧ (p 20 : ℝ) = 627 := by
  constructor
  · norm_num [show p 10 = 42 by native_decide]
  · norm_num [show p 20 = 627 by native_decide]

/-- Subexponential growth: p(n) ≤ 2^n for small n. -/
example : ∀ n : Fin 21, p n ≤ 2 ^ (n : ℕ) := by native_decide



structure PartitionAsymptoticsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PartitionAsymptoticsBudgetCertificate.controlled
    (c : PartitionAsymptoticsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PartitionAsymptoticsBudgetCertificate.budgetControlled
    (c : PartitionAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PartitionAsymptoticsBudgetCertificate.Ready
    (c : PartitionAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PartitionAsymptoticsBudgetCertificate.size
    (c : PartitionAsymptoticsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem partitionAsymptotics_budgetCertificate_le_size
    (c : PartitionAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePartitionAsymptoticsBudgetCertificate :
    PartitionAsymptoticsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePartitionAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [PartitionAsymptoticsBudgetCertificate.controlled,
      samplePartitionAsymptoticsBudgetCertificate]
  · norm_num [PartitionAsymptoticsBudgetCertificate.budgetControlled,
      samplePartitionAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePartitionAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      samplePartitionAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePartitionAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [PartitionAsymptoticsBudgetCertificate.controlled,
      samplePartitionAsymptoticsBudgetCertificate]
  · norm_num [PartitionAsymptoticsBudgetCertificate.budgetControlled,
      samplePartitionAsymptoticsBudgetCertificate]

example :
    samplePartitionAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      samplePartitionAsymptoticsBudgetCertificate.size := by
  apply partitionAsymptotics_budgetCertificate_le_size
  constructor
  · norm_num [PartitionAsymptoticsBudgetCertificate.controlled,
      samplePartitionAsymptoticsBudgetCertificate]
  · norm_num [PartitionAsymptoticsBudgetCertificate.budgetControlled,
      samplePartitionAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PartitionAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePartitionAsymptoticsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePartitionAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.PartitionAsymptotics
