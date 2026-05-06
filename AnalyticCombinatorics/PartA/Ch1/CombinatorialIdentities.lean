import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.CombinatorialIdentities

open Finset


/-!
Chapter I/III finite checks for binomial coefficient identities used as
standard tools in analytic combinatorics.
-/

/-! ## Vandermonde and Pascal -/

/-- Mathlib's form of Vandermonde's identity. -/
theorem vandermonde_identity (m n r : ℕ) :
    Nat.choose (m + n) r =
      ∑ ij ∈ Finset.antidiagonal r, Nat.choose m ij.1 * Nat.choose n ij.2 := by
  exact Nat.add_choose_eq m n r

/-- Vandermonde's identity at `(m,n,r) = (5,3,4)`, written as a range sum. -/
theorem vandermonde_5_3_4_range :
    Nat.choose (5 + 3) 4 =
      ∑ k ∈ Finset.range (4 + 1), Nat.choose 5 k * Nat.choose 3 (4 - k) := by
  native_decide

/-- The nonzero terms in the same Vandermonde check. -/
theorem vandermonde_5_3_4_terms :
    Nat.choose 8 4 =
      Nat.choose 5 1 * Nat.choose 3 3 +
      Nat.choose 5 2 * Nat.choose 3 2 +
      Nat.choose 5 3 * Nat.choose 3 1 +
      Nat.choose 5 4 * Nat.choose 3 0 := by
  native_decide

theorem vandermonde_5_3_4_value :
    Nat.choose 8 4 = 70 := by
  native_decide

theorem vandermonde_5_3_4_arithmetic :
    70 = 5 * 1 + 10 * 3 + 10 * 3 + 5 * 1 := by
  native_decide

/-- Pascal's rule, checked for `1 ≤ k ≤ n ≤ 8`. -/
theorem pascal_rule_1_8 :
    ∀ n ∈ Finset.Icc 1 8, ∀ k ∈ Finset.Icc 1 n,
      Nat.choose n k = Nat.choose (n - 1) (k - 1) + Nat.choose (n - 1) k := by
  intro n hn k hk
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  rcases Finset.mem_Icc.mp hk with ⟨hklo, hkhi⟩
  interval_cases n <;> interval_cases k <;> native_decide

/-! ## Hockey-stick identity -/

theorem hockey_stick_5_2 :
    (∑ i ∈ Finset.Icc 2 5, Nat.choose i 2) = Nat.choose 6 3 := by
  native_decide

theorem hockey_stick_5_2_value :
    Nat.choose 2 2 + Nat.choose 3 2 + Nat.choose 4 2 + Nat.choose 5 2 = 20 ∧
      Nat.choose 6 3 = 20 := by
  native_decide

/-! ## Binomial sums -/

theorem binomial_sum_eq_two_pow_0_10 :
    ∀ n ∈ Finset.Icc 0 10,
      (∑ k ∈ Finset.range (n + 1), Nat.choose n k) = 2 ^ n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

theorem alternating_binomial_sum_eq_zero_1_10 :
    ∀ n ∈ Finset.Icc 1 10,
      (∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ k) * (Nat.choose n k : ℤ)) = 0 := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

theorem binomial_square_sum_0_8 :
    ∀ n ∈ Finset.Icc 0 8,
      (∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2) = Nat.choose (2 * n) n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

theorem weighted_binomial_sum_1_8 :
    ∀ n ∈ Finset.Icc 1 8,
      (∑ k ∈ Finset.range (n + 1), k * Nat.choose n k) = n * 2 ^ (n - 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

/-! ## Double-counting identities -/

theorem two_n_choose_two_1_8 :
    ∀ n ∈ Finset.Icc 1 8,
      Nat.choose (2 * n) 2 = 2 * Nat.choose n 2 + n ^ 2 := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

theorem sum_squares_1_10 :
    ∀ n ∈ Finset.Icc 1 10,
      (∑ k ∈ Finset.Icc 1 n, k ^ 2) = n * (n + 1) * (2 * n + 1) / 6 := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

/-! ## Catalan numbers -/

/-- Catalan numbers from the usual convolution recurrence. -/
def catalanNumber : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k : (Finset.range (n + 1) : Set ℕ),
        catalanNumber k.1 * catalanNumber (n - k.1)
termination_by n => n
decreasing_by
  all_goals simp_wf
  all_goals
    try
      have hk := Finset.mem_range.mp (show k.1 ∈ Finset.range (n + 1) from k.2)
    omega

theorem catalanNumber_zero : catalanNumber 0 = 1 := by
  native_decide

theorem catalanNumber_succ (n : ℕ) :
    catalanNumber (n + 1) =
      ∑ k ∈ Finset.range (n + 1), catalanNumber k * catalanNumber (n - k) := by
  rw [catalanNumber]
  exact Finset.sum_coe_sort (s := Finset.range (n + 1))
    (f := fun k : ℕ => catalanNumber k * catalanNumber (n - k))

theorem catalan_formula_0_10 :
    ∀ n ∈ Finset.Icc 0 10,
      catalanNumber n = Nat.choose (2 * n) n / (n + 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

theorem catalan_convolution_0_8 :
    ∀ n ∈ Finset.Icc 0 8,
      (∑ k ∈ Finset.range (n + 1), catalanNumber k * catalanNumber (n - k)) =
        catalanNumber (n + 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide



structure CombinatorialIdentitiesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CombinatorialIdentitiesBudgetCertificate.controlled
    (c : CombinatorialIdentitiesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CombinatorialIdentitiesBudgetCertificate.budgetControlled
    (c : CombinatorialIdentitiesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CombinatorialIdentitiesBudgetCertificate.Ready
    (c : CombinatorialIdentitiesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CombinatorialIdentitiesBudgetCertificate.size
    (c : CombinatorialIdentitiesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem combinatorialIdentities_budgetCertificate_le_size
    (c : CombinatorialIdentitiesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCombinatorialIdentitiesBudgetCertificate :
    CombinatorialIdentitiesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCombinatorialIdentitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatorialIdentitiesBudgetCertificate.controlled,
      sampleCombinatorialIdentitiesBudgetCertificate]
  · norm_num [CombinatorialIdentitiesBudgetCertificate.budgetControlled,
      sampleCombinatorialIdentitiesBudgetCertificate]

example :
    sampleCombinatorialIdentitiesBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatorialIdentitiesBudgetCertificate.size := by
  apply combinatorialIdentities_budgetCertificate_le_size
  constructor
  · norm_num [CombinatorialIdentitiesBudgetCertificate.controlled,
      sampleCombinatorialIdentitiesBudgetCertificate]
  · norm_num [CombinatorialIdentitiesBudgetCertificate.budgetControlled,
      sampleCombinatorialIdentitiesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCombinatorialIdentitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatorialIdentitiesBudgetCertificate.controlled,
      sampleCombinatorialIdentitiesBudgetCertificate]
  · norm_num [CombinatorialIdentitiesBudgetCertificate.budgetControlled,
      sampleCombinatorialIdentitiesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCombinatorialIdentitiesBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatorialIdentitiesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CombinatorialIdentitiesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCombinatorialIdentitiesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCombinatorialIdentitiesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.CombinatorialIdentities
