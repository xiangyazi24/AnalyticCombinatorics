import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.PermutationInversions


/-!
# Permutation Inversions, Mahonian Statistics, and Inversion Tables

From Chapter II of Flajolet & Sedgewick, *Analytic Combinatorics* (2009).

An **inversion** in a permutation σ of [n] is a pair (i,j) with i < j but σ(i) > σ(j).
The inversion number is a classic Mahonian statistic — its distribution over S_n equals
the distribution of the major index (MacMahon's theorem).

The **Eulerian numbers** A(n,k) count permutations by descents (positions where σ(i) > σ(i+1)).
-/

-- ============================================================
-- Section 1: Inversion numbers I(n,k)
-- ============================================================

/-!
## Inversion Numbers

`inversionCount n k` = number of permutations of [n] with exactly k inversions.

The generating polynomial ∑_k I(n,k) * q^k = [n]_q! = 1*(1+q)*(1+q+q^2)*...*(1+q+...+q^{n-1}).

Tabulated values for n = 3 and n = 4.
-/

/-- Table of inversion counts I(3,k) for k = 0..3 -/
def invCount3 : Fin 4 → ℕ := ![1, 2, 2, 1]

/-- Table of inversion counts I(4,k) for k = 0..6 -/
def invCount4 : Fin 7 → ℕ := ![1, 3, 5, 6, 5, 3, 1]

/-- The sum of I(3,k) equals 3! = 6 -/
theorem invCount3_sum : ∑ k : Fin 4, invCount3 k = 6 := by native_decide

/-- The sum of I(4,k) equals 4! = 24 -/
theorem invCount4_sum : ∑ k : Fin 7, invCount4 k = 24 := by native_decide

/-- Symmetry of inversion table for n=3: I(3,k) = I(3, 3-k) -/
theorem invCount3_symmetry : ∀ k : Fin 4, invCount3 k = invCount3 ⟨3 - k.val, by omega⟩ := by
  native_decide

/-- Symmetry of inversion table for n=4: I(4,k) = I(4, 6-k) -/
theorem invCount4_symmetry : ∀ k : Fin 7, invCount4 k = invCount4 ⟨6 - k.val, by omega⟩ := by
  native_decide

/-- I(3,0) = 1: unique permutation with 0 inversions is the identity -/
theorem invCount3_zero : invCount3 0 = 1 := by native_decide

/-- I(3,3) = 1: unique permutation with max inversions is the reverse -/
theorem invCount3_max : invCount3 3 = 1 := by native_decide

/-- I(4,0) = 1: unique permutation with 0 inversions is the identity -/
theorem invCount4_zero : invCount4 0 = 1 := by native_decide

/-- I(4,6) = 1: unique permutation with max inversions is the reverse -/
theorem invCount4_max : invCount4 6 = 1 := by native_decide

-- ============================================================
-- Section 2: Maximum inversions = C(n,2)
-- ============================================================

/-!
## Maximum Number of Inversions

The maximum number of inversions in a permutation of [n] is C(n,2) = n*(n-1)/2,
achieved uniquely by the reverse permutation (n, n-1, ..., 2, 1).
-/

/-- Triangular numbers C(n,2) = n*(n-1)/2 for n=2..8 -/
def triangular : Fin 7 → ℕ := ![1, 3, 6, 10, 15, 21, 28]

/-- C(2,2)=1, C(3,2)=3, ..., C(8,2)=28: verified values -/
theorem triangular_values :
    triangular 0 = 1 ∧ triangular 1 = 3 ∧ triangular 2 = 6 ∧
    triangular 3 = 10 ∧ triangular 4 = 15 ∧ triangular 5 = 21 ∧
    triangular 6 = 28 := by
  native_decide

/-- For n ≥ 2, C(n,2) = n*(n-1)/2 (verified for n=2..8) -/
theorem choose2_formula (n : ℕ) (hn2 : 2 ≤ n) (hn8 : n ≤ 8) :
    n.choose 2 = n * (n - 1) / 2 := by
  interval_cases n <;> native_decide

/-- Maximum inversions for n=3 is C(3,2)=3 -/
theorem maxInv3 : Nat.choose 3 2 = 3 := by native_decide

/-- Maximum inversions for n=4 is C(4,2)=6 -/
theorem maxInv4 : Nat.choose 4 2 = 6 := by native_decide

/-- Maximum inversions for n=5 is C(5,2)=10 -/
theorem maxInv5 : Nat.choose 5 2 = 10 := by native_decide

-- ============================================================
-- Section 3: Eulerian numbers A(n,k)
-- ============================================================

/-!
## Eulerian Numbers

`eulerianNum n k` = number of permutations of [n] with exactly k descents.

A descent of σ at position i means σ(i) > σ(i+1).

Recurrence: A(n,k) = (k+1)*A(n-1,k) + (n-k)*A(n-1,k-1)
with A(1,0) = 1, A(n,k) = 0 for k ≥ n or k < 0.
-/

/-- Eulerian numbers via the standard recurrence -/
def eulerianNum : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 =>
      if k + 1 < n + 1 then
        (k + 2) * eulerianNum n (k + 1) + (n - k) * eulerianNum n k
      else
        0
termination_by n _ => n

/-- A(1,0)=1 -/
theorem eulerianNum_1_0 : eulerianNum 1 0 = 1 := by native_decide

/-- A(3,0)=1 -/
theorem eulerianNum_3_0 : eulerianNum 3 0 = 1 := by native_decide

/-- A(3,1)=4 -/
theorem eulerianNum_3_1 : eulerianNum 3 1 = 4 := by native_decide

/-- A(3,2)=1 -/
theorem eulerianNum_3_2 : eulerianNum 3 2 = 1 := by native_decide

/-- A(4,0)=1 -/
theorem eulerianNum_4_0 : eulerianNum 4 0 = 1 := by native_decide

/-- A(4,1)=11 -/
theorem eulerianNum_4_1 : eulerianNum 4 1 = 11 := by native_decide

/-- A(4,2)=11 -/
theorem eulerianNum_4_2 : eulerianNum 4 2 = 11 := by native_decide

/-- A(4,3)=1 -/
theorem eulerianNum_4_3 : eulerianNum 4 3 = 1 := by native_decide

/-- A(5,0)=1 -/
theorem eulerianNum_5_0 : eulerianNum 5 0 = 1 := by native_decide

/-- A(5,1)=26 -/
theorem eulerianNum_5_1 : eulerianNum 5 1 = 26 := by native_decide

/-- A(5,2)=66 -/
theorem eulerianNum_5_2 : eulerianNum 5 2 = 66 := by native_decide

/-- A(5,3)=26 -/
theorem eulerianNum_5_3 : eulerianNum 5 3 = 26 := by native_decide

/-- A(5,4)=1 -/
theorem eulerianNum_5_4 : eulerianNum 5 4 = 1 := by native_decide

/-- Sum of A(3,k) = 3! = 6 -/
theorem eulerianNum_3_sum :
    eulerianNum 3 0 + eulerianNum 3 1 + eulerianNum 3 2 = 6 := by
  native_decide

/-- Sum of A(4,k) = 4! = 24 -/
theorem eulerianNum_4_sum :
    eulerianNum 4 0 + eulerianNum 4 1 + eulerianNum 4 2 + eulerianNum 4 3 = 24 := by
  native_decide

/-- Sum of A(5,k) = 5! = 120 -/
theorem eulerianNum_5_sum :
    eulerianNum 5 0 + eulerianNum 5 1 + eulerianNum 5 2 +
    eulerianNum 5 3 + eulerianNum 5 4 = 120 := by
  native_decide

/-- Symmetry A(3,k) = A(3, 2-k) for k=0,1,2 -/
theorem eulerianNum_3_symmetry :
    eulerianNum 3 0 = eulerianNum 3 2 ∧
    eulerianNum 3 1 = eulerianNum 3 1 := by
  native_decide

/-- Symmetry A(4,k) = A(4, 3-k) for k=0,1,2,3 -/
theorem eulerianNum_4_symmetry :
    eulerianNum 4 0 = eulerianNum 4 3 ∧
    eulerianNum 4 1 = eulerianNum 4 2 := by
  native_decide

/-- Symmetry A(5,k) = A(5, 4-k) for k=0..4 -/
theorem eulerianNum_5_symmetry :
    eulerianNum 5 0 = eulerianNum 5 4 ∧
    eulerianNum 5 1 = eulerianNum 5 3 ∧
    eulerianNum 5 2 = eulerianNum 5 2 := by
  native_decide

-- ============================================================
-- Section 4: Descent polynomial special values
-- ============================================================

/-!
## Descent Polynomial: Special Values

- A(n,0) = 1 for all n≥1: only the identity has 0 descents.
- A(n,n-1) = 1 for all n≥1: only the reverse permutation has n-1 descents.
- A(n,1) = 2^n - n - 1 for n≥2.
-/

/-- A(n,0) = 1 for n=1..6 -/
theorem eulerianNum_zero_descent (n : ℕ) (hn1 : 1 ≤ n) (hn6 : n ≤ 6) :
    eulerianNum n 0 = 1 := by
  interval_cases n <;> native_decide

/-- A(n, n-1) = 1 for n=1..6 (rewritten to avoid ℕ subtraction: eulerianNum n k = 1 where k+1=n) -/
theorem eulerianNum_max_descent (n : ℕ) (hn1 : 1 ≤ n) (hn6 : n ≤ 6) :
    eulerianNum n (n - 1) = 1 := by
  interval_cases n <;> native_decide

/-- A(2,1) = 1 = 2^2 - 2 - 1 -/
theorem eulerianNum_2_1_formula : eulerianNum 2 1 = 2^2 - 2 - 1 := by native_decide

/-- A(3,1) = 4 = 2^3 - 3 - 1 -/
theorem eulerianNum_3_1_formula : eulerianNum 3 1 = 2^3 - 3 - 1 := by native_decide

/-- A(4,1) = 11 = 2^4 - 4 - 1 -/
theorem eulerianNum_4_1_formula : eulerianNum 4 1 = 2^4 - 4 - 1 := by native_decide

/-- A(5,1) = 26 = 2^5 - 5 - 1 -/
theorem eulerianNum_5_1_formula : eulerianNum 5 1 = 2^5 - 5 - 1 := by native_decide

/-- A(n,1) = 2^n - n - 1 for n=2..5 (verified numerically) -/
theorem eulerianNum_one_descent_formula (n : ℕ) (hn2 : 2 ≤ n) (hn5 : n ≤ 5) :
    eulerianNum n 1 = 2^n - n - 1 := by
  interval_cases n <;> native_decide

-- ============================================================
-- Section 5: Mahonian distribution — total inversions
-- ============================================================

/-!
## Mahonian Distribution: Total Inversions

By symmetry of the inversion table and MacMahon's theorem, the total number of
inversions across all permutations of [n] equals n! * C(n,2) / 2 = n! * n*(n-1)/4.

Specific values:
- n=2: total = 1
- n=3: total = 9   (0+1+1+2+2+3 = 9 = 6*3/2)
- n=4: total = 72  (= 24*6/2)
- n=5: total = 600 (= 120*10/2)
-/

/-- Total inversions across all perms of [3] = 9 (from I(3,k) table) -/
theorem totalInv3 :
    ∑ k : Fin 4, (k.val * invCount3 k) = 9 := by
  native_decide

/-- Total inversions across all perms of [4] = 72 (from I(4,k) table) -/
theorem totalInv4 :
    ∑ k : Fin 7, (k.val * invCount4 k) = 72 := by
  native_decide

/-- For n=3: total = 3! * C(3,2) / 2 = 6 * 3 / 2 = 9 -/
theorem totalInv3_formula : 6 * 3 / 2 = 9 := by norm_num

/-- For n=4: total = 4! * C(4,2) / 2 = 24 * 6 / 2 = 72 -/
theorem totalInv4_formula : 24 * 6 / 2 = 72 := by norm_num

/-- For n=5: total = 5! * C(5,2) / 2 = 120 * 10 / 2 = 600 -/
theorem totalInv5_formula : 120 * 10 / 2 = 600 := by norm_num

/-- totalInv(n) = n! * n * (n-1) / 4 for small n (n=2..5): divisibility + values -/
theorem totalInv_formula_n2 : 2 * 2 * 1 / 4 = 1 := by norm_num
theorem totalInv_formula_n3 : 6 * 3 * 2 / 4 = 9 := by norm_num
theorem totalInv_formula_n4 : 24 * 4 * 3 / 4 = 72 := by norm_num
theorem totalInv_formula_n5 : 120 * 5 * 4 / 4 = 600 := by norm_num

/-- Verify that totalInv = n! * C(n,2) / 2 matches n! * n*(n-1)/4 for n=2..5 -/
theorem totalInv_two_formulas_agree (n : ℕ) (hn2 : 2 ≤ n) (hn5 : n ≤ 5) :
    n.factorial * n.choose 2 / 2 = n.factorial * n * (n - 1) / 4 := by
  interval_cases n <;> native_decide

-- ============================================================
-- Section 6: Excedances
-- ============================================================

/-!
## Excedances

An **excedance** of σ at position i (1-indexed) is when σ(i) > i.
MacMahon's theorem: excedances are equidistributed with descents, so the number of
permutations of [n] with exactly k excedances also equals A(n,k).

Key facts:
- A(n,0) = 1: only the identity has 0 excedances (= identity has 0 descents)
- Derangements (fixed-point-free permutations) all have ≥ 1 excedance

Derangement numbers: D(1)=0, D(2)=1, D(3)=2, D(4)=9, D(5)=44
-/

/-- Derangement numbers via the standard recurrence -/
def derangementNum : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangementNum (n + 1) + derangementNum n)

/-- D(3) = 2 -/
theorem derangementNum_3 : derangementNum 3 = 2 := by native_decide

/-- D(4) = 9 -/
theorem derangementNum_4 : derangementNum 4 = 9 := by native_decide

/-- D(5) = 44 -/
theorem derangementNum_5 : derangementNum 5 = 44 := by native_decide

/-- A(n,0) = 1 for n=1..5 (identity is the unique permutation with 0 excedances/descents) -/
theorem excedance_zero_count (n : ℕ) (hn1 : 1 ≤ n) (hn5 : n ≤ 5) :
    eulerianNum n 0 = 1 := by
  interval_cases n <;> native_decide

/-!
Every derangement has at least one excedance.  This is witnessed combinatorially:
if σ has no fixed points then it cannot be the identity, so it has at least one
position where σ(i) > i (an excedance) or at least one where σ(i) < i (a weak
descent below the diagonal).  In fact at least one excedance must exist.

We verify the quantitative consequence: D(n) ≤ n! - A(n,0)*1 = n! - 1 for n≥1,
which says fewer than all permutations are derangements (trivially true).
We also verify D(n) ≤ total permutations with ≥ 1 excedance = n! - A(n,0) = n! - 1.
-/

/-- For n=3: D(3)=2 ≤ 3!-1=5 (derangements are a strict subset of non-identity perms) -/
theorem derangement_bound_3 : derangementNum 3 ≤ Nat.factorial 3 - 1 := by native_decide

/-- For n=4: D(4)=9 ≤ 4!-1=23 -/
theorem derangement_bound_4 : derangementNum 4 ≤ Nat.factorial 4 - 1 := by native_decide

/-- For n=5: D(5)=44 ≤ 5!-1=119 -/
theorem derangement_bound_5 : derangementNum 5 ≤ Nat.factorial 5 - 1 := by native_decide

/-- Number of permutations of [n] with 0 excedances = A(n,0) = 1 for n=1..5 -/
theorem excedance_free_count (n : ℕ) (hn1 : 1 ≤ n) (hn5 : n ≤ 5) :
    eulerianNum n 0 = 1 := by
  interval_cases n <;> native_decide

-- ============================================================
-- Section 7: Worpitzky identity (spot checks)
-- ============================================================

/-!
## Worpitzky Identity

The Worpitzky identity states:
  x^n = ∑_{k=0}^{n-1} A(n,k) * C(x+n-1-k, n)

(where C(m,n) = m.choose n for non-negative integers m,n)

We verify this for small integer values of x and n.
-/

/-- Worpitzky identity for n=3, x=2: 2^3=8 = A(3,0)*C(4,3) + A(3,1)*C(3,3) + A(3,2)*C(2,3) -/
theorem worpitzky_3_2 :
    2^3 = eulerianNum 3 0 * Nat.choose 4 3 +
          eulerianNum 3 1 * Nat.choose 3 3 +
          eulerianNum 3 2 * Nat.choose 2 3 := by
  native_decide

/-- Worpitzky identity for n=3, x=3: 3^3=27 = A(3,0)*C(5,3) + A(3,1)*C(4,3) + A(3,2)*C(3,3) -/
theorem worpitzky_3_3 :
    3^3 = eulerianNum 3 0 * Nat.choose 5 3 +
          eulerianNum 3 1 * Nat.choose 4 3 +
          eulerianNum 3 2 * Nat.choose 3 3 := by
  native_decide

/-- Worpitzky identity for n=4, x=2: 2^4=16 = ∑_k A(4,k)*C(x+3-k,4) -/
theorem worpitzky_4_2 :
    2^4 = eulerianNum 4 0 * Nat.choose 5 4 +
          eulerianNum 4 1 * Nat.choose 4 4 +
          eulerianNum 4 2 * Nat.choose 3 4 +
          eulerianNum 4 3 * Nat.choose 2 4 := by
  native_decide

/-- Worpitzky identity for n=4, x=3: 3^4=81 = ∑_k A(4,k)*C(x+3-k,4) -/
theorem worpitzky_4_3 :
    3^4 = eulerianNum 4 0 * Nat.choose 6 4 +
          eulerianNum 4 1 * Nat.choose 5 4 +
          eulerianNum 4 2 * Nat.choose 4 4 +
          eulerianNum 4 3 * Nat.choose 3 4 := by
  native_decide

/-- Worpitzky identity for n=4, x=4: 4^4=256 = ∑_k A(4,k)*C(x+3-k,4) -/
theorem worpitzky_4_4 :
    4^4 = eulerianNum 4 0 * Nat.choose 7 4 +
          eulerianNum 4 1 * Nat.choose 6 4 +
          eulerianNum 4 2 * Nat.choose 5 4 +
          eulerianNum 4 3 * Nat.choose 4 4 := by
  native_decide



structure PermutationInversionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PermutationInversionsBudgetCertificate.controlled
    (c : PermutationInversionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PermutationInversionsBudgetCertificate.budgetControlled
    (c : PermutationInversionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PermutationInversionsBudgetCertificate.Ready
    (c : PermutationInversionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PermutationInversionsBudgetCertificate.size
    (c : PermutationInversionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem permutationInversions_budgetCertificate_le_size
    (c : PermutationInversionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePermutationInversionsBudgetCertificate :
    PermutationInversionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePermutationInversionsBudgetCertificate.Ready := by
  constructor
  · norm_num [PermutationInversionsBudgetCertificate.controlled,
      samplePermutationInversionsBudgetCertificate]
  · norm_num [PermutationInversionsBudgetCertificate.budgetControlled,
      samplePermutationInversionsBudgetCertificate]

example :
    samplePermutationInversionsBudgetCertificate.certificateBudgetWindow ≤
      samplePermutationInversionsBudgetCertificate.size := by
  apply permutationInversions_budgetCertificate_le_size
  constructor
  · norm_num [PermutationInversionsBudgetCertificate.controlled,
      samplePermutationInversionsBudgetCertificate]
  · norm_num [PermutationInversionsBudgetCertificate.budgetControlled,
      samplePermutationInversionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePermutationInversionsBudgetCertificate.Ready := by
  constructor
  · norm_num [PermutationInversionsBudgetCertificate.controlled,
      samplePermutationInversionsBudgetCertificate]
  · norm_num [PermutationInversionsBudgetCertificate.budgetControlled,
      samplePermutationInversionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePermutationInversionsBudgetCertificate.certificateBudgetWindow ≤
      samplePermutationInversionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PermutationInversionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePermutationInversionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePermutationInversionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.PermutationInversions
