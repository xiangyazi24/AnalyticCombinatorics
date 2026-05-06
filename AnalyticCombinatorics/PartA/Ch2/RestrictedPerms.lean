import Mathlib.Tactic

namespace AnalyticCombinatorics.PartA.Ch2.RestrictedPerms

open Finset

set_option linter.style.nativeDecide false

/-- Number of permutations of `n` labelled atoms whose cycle lengths are all at
most `m`.

The recurrence isolates the cycle containing a distinguished atom.  If this
cycle has length `k + 1`, choose the other `k` atoms, arrange them cyclically in
`k!` ways, and recursively permute the remaining atoms. -/
def boundedCyclePermCount (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k ∈ Finset.range (n + 1),
        if k + 1 ≤ m then
          n.choose k * k.factorial * boundedCyclePermCount m (n - k)
        else
          0
termination_by n => n
decreasing_by omega

theorem boundedCyclePermCount_one_checked (n : ℕ) (hn : n ≤ 8) :
    boundedCyclePermCount 1 n = 1 := by
  interval_cases n <;> native_decide

theorem boundedCyclePermCount_large_checked (n : ℕ) (hn : n ≤ 8) :
    boundedCyclePermCount n n = n.factorial := by
  interval_cases n <;> native_decide

theorem boundedCyclePermCount_two_zero : boundedCyclePermCount 2 0 = 1 := by native_decide
theorem boundedCyclePermCount_two_one : boundedCyclePermCount 2 1 = 1 := by native_decide
theorem boundedCyclePermCount_two_two : boundedCyclePermCount 2 2 = 2 := by native_decide
theorem boundedCyclePermCount_two_three : boundedCyclePermCount 2 3 = 4 := by native_decide
theorem boundedCyclePermCount_two_four : boundedCyclePermCount 2 4 = 10 := by native_decide
theorem boundedCyclePermCount_two_five : boundedCyclePermCount 2 5 = 26 := by native_decide
theorem boundedCyclePermCount_two_six : boundedCyclePermCount 2 6 = 76 := by native_decide

/-- Number of permutations of `n` labelled atoms with no fixed points and no
2-cycles.  Equivalently, all cycle lengths are at least `3`. -/
def noFixedNo2Count : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k ∈ Finset.range (n + 1),
        if 3 ≤ k + 1 then
          n.choose k * k.factorial * noFixedNo2Count (n - k)
        else
          0
termination_by n => n
decreasing_by omega

theorem noFixedNo2Count_zero : noFixedNo2Count 0 = 1 := by native_decide
theorem noFixedNo2Count_one : noFixedNo2Count 1 = 0 := by native_decide
theorem noFixedNo2Count_two : noFixedNo2Count 2 = 0 := by native_decide
theorem noFixedNo2Count_three : noFixedNo2Count 3 = 2 := by native_decide
theorem noFixedNo2Count_four : noFixedNo2Count 4 = 6 := by native_decide
theorem noFixedNo2Count_five : noFixedNo2Count 5 = 24 := by native_decide
theorem noFixedNo2Count_six : noFixedNo2Count 6 = 160 := by native_decide

/-- The Entringer triangle, in the Seidel form.  Its diagonal entries are the
Euler zigzag numbers. -/
def zigzagTriangle : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      if k + 1 ≤ n + 1 then
        zigzagTriangle (n + 1) k + zigzagTriangle n (n - k)
      else
        0
termination_by n k => (n, k)
decreasing_by all_goals simp_wf; omega

/-- Euler zigzag numbers: alternating permutations of `n` labelled atoms. -/
def zigzagCount (n : ℕ) : ℕ :=
  zigzagTriangle n n

theorem zigzagCount_zero : zigzagCount 0 = 1 := by native_decide
theorem zigzagCount_one : zigzagCount 1 = 1 := by native_decide
theorem zigzagCount_two : zigzagCount 2 = 1 := by native_decide
theorem zigzagCount_three : zigzagCount 3 = 2 := by native_decide
theorem zigzagCount_four : zigzagCount 4 = 5 := by native_decide
theorem zigzagCount_five : zigzagCount 5 = 16 := by native_decide
theorem zigzagCount_six : zigzagCount 6 = 61 := by native_decide

/-- Checked instances of the tangent/secant convolution recurrence
`2 E(n) = sum_{k=0}^{n-1} binom(n-1,k) E(k) E(n-1-k)`, for `2 ≤ n ≤ 7`. -/
theorem zigzagCount_convolution_checked (n : ℕ) (hn₁ : 2 ≤ n) (hn₂ : n ≤ 7) :
    2 * zigzagCount n =
      ∑ k ∈ Finset.range n,
        (n - 1).choose k * zigzagCount k * zigzagCount (n - 1 - k) := by
  interval_cases n <;> native_decide


structure RestrictedPermsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RestrictedPermsBudgetCertificate.controlled
    (c : RestrictedPermsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RestrictedPermsBudgetCertificate.budgetControlled
    (c : RestrictedPermsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RestrictedPermsBudgetCertificate.Ready
    (c : RestrictedPermsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RestrictedPermsBudgetCertificate.size
    (c : RestrictedPermsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem restrictedPerms_budgetCertificate_le_size
    (c : RestrictedPermsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRestrictedPermsBudgetCertificate :
    RestrictedPermsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRestrictedPermsBudgetCertificate.Ready := by
  constructor
  · norm_num [RestrictedPermsBudgetCertificate.controlled,
      sampleRestrictedPermsBudgetCertificate]
  · norm_num [RestrictedPermsBudgetCertificate.budgetControlled,
      sampleRestrictedPermsBudgetCertificate]

example :
    sampleRestrictedPermsBudgetCertificate.certificateBudgetWindow ≤
      sampleRestrictedPermsBudgetCertificate.size := by
  apply restrictedPerms_budgetCertificate_le_size
  constructor
  · norm_num [RestrictedPermsBudgetCertificate.controlled,
      sampleRestrictedPermsBudgetCertificate]
  · norm_num [RestrictedPermsBudgetCertificate.budgetControlled,
      sampleRestrictedPermsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRestrictedPermsBudgetCertificate.Ready := by
  constructor
  · norm_num [RestrictedPermsBudgetCertificate.controlled,
      sampleRestrictedPermsBudgetCertificate]
  · norm_num [RestrictedPermsBudgetCertificate.budgetControlled,
      sampleRestrictedPermsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRestrictedPermsBudgetCertificate.certificateBudgetWindow ≤
      sampleRestrictedPermsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RestrictedPermsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRestrictedPermsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRestrictedPermsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.RestrictedPerms
