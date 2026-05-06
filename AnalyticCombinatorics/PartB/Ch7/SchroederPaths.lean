import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch7.SchroederPaths


/-!
  Chapter VII executable tables for Schroeder paths and nearby lattice paths.

  The data are intentionally finite: each theorem is a bounded computation
  certified by `native_decide`.
-/

/-! ## Large and small Schroeder numbers -/

/-- Catalan number `C_n = binom(2n,n)/(n+1)`. -/
def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Large Schroeder numbers from `S_n = sum_k C_k * binom(n+k,n-k)`. -/
def largeSchroederFormula (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    catalanNumber k * Nat.choose (n + k) (n - k)

/-- Small Schroeder numbers: `s_0 = 1`, and `s_n = S_n / 2` for `n > 0`. -/
def smallSchroederFormula (n : ℕ) : ℕ :=
  if n = 0 then 1 else largeSchroederFormula n / 2

/-- Large Schroeder numbers `S_0, ..., S_11`. -/
def largeSchroederTable : Fin 12 → ℕ :=
  ![1, 2, 6, 22, 90, 394, 1806, 8558, 41586, 206098, 1037718, 5293446]

/-- Small Schroeder numbers `s_0, ..., s_11`. -/
def smallSchroederTable : Fin 12 → ℕ :=
  ![1, 1, 3, 11, 45, 197, 903, 4279, 20793, 103049, 518859, 2646723]

theorem largeSchroeder_table_matches_formula :
    ∀ n : Fin 12, largeSchroederFormula n = largeSchroederTable n := by
  native_decide

theorem smallSchroeder_table_matches_formula :
    ∀ n : Fin 12, smallSchroederFormula n = smallSchroederTable n := by
  native_decide

theorem smallSchroeder_half_large_after_zero :
    ∀ n : Fin 12, 0 < (n : ℕ) →
      2 * smallSchroederTable n = largeSchroederTable n := by
  native_decide

theorem largeSchroeder_initial_growth_window :
    ∀ n : Fin 12, 1 ≤ (n : ℕ) →
      largeSchroederTable n < 6 ^ (n : ℕ) := by
  native_decide

/-! ## Delannoy numbers -/

/-- Delannoy number closed form `D(m,n) = sum_k binom(m,k) binom(n,k) 2^k`. -/
def delannoyFormula (m n : ℕ) : ℕ :=
  (Finset.range (Nat.min m n + 1)).sum fun k =>
    Nat.choose m k * Nat.choose n k * 2 ^ k

/-- Delannoy table `D(m,n)` for `0 <= m,n <= 6`. -/
def delannoyTable : Fin 7 → Fin 7 → ℕ :=
  ![
    ![1, 1, 1, 1, 1, 1, 1],
    ![1, 3, 5, 7, 9, 11, 13],
    ![1, 5, 13, 25, 41, 61, 85],
    ![1, 7, 25, 63, 129, 231, 377],
    ![1, 9, 41, 129, 321, 681, 1289],
    ![1, 11, 61, 231, 681, 1683, 3653],
    ![1, 13, 85, 377, 1289, 3653, 8989]
  ]

/-- Central Delannoy numbers `D(n,n)` for `0 <= n <= 11`. -/
def centralDelannoyTable : Fin 12 → ℕ :=
  ![1, 3, 13, 63, 321, 1683, 8989, 48639, 265729, 1462563, 8097453, 45046719]

theorem delannoy_table_matches_formula :
    ∀ m : Fin 7, ∀ n : Fin 7,
      delannoyFormula m n = delannoyTable m n := by
  native_decide

theorem delannoy_table_symmetric :
    ∀ m : Fin 7, ∀ n : Fin 7,
      delannoyTable m n = delannoyTable n m := by
  native_decide

theorem centralDelannoy_table_matches_formula :
    ∀ n : Fin 12, delannoyFormula n n = centralDelannoyTable n := by
  native_decide

theorem centralDelannoy_odd :
    ∀ n : Fin 12, centralDelannoyTable n % 2 = 1 := by
  native_decide

/-! ## Height and area distributions for small Schroeder paths -/

/-- Sum a length-seven table. -/
def sumFin7 (f : Fin 7 → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin 7)).sum fun i => f i

/--
Rows are semilength `n = 0, ..., 6`; columns are exact maximum height
`h = 0, ..., 6`.
-/
def heightDistribution : Fin 7 → Fin 7 → ℕ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0],
    ![1, 4, 1, 0, 0, 0, 0],
    ![1, 12, 8, 1, 0, 0, 0],
    ![1, 33, 43, 12, 1, 0, 0],
    ![1, 88, 197, 91, 16, 1, 0],
    ![1, 232, 833, 564, 155, 20, 1]
  ]

theorem heightDistribution_rows_sum_to_largeSchroeder :
    ∀ n : Fin 7, sumFin7 (heightDistribution n) = largeSchroederFormula n := by
  native_decide

theorem heightDistribution_peak_at_most_semilength :
    ∀ n : Fin 7, ∀ h : Fin 7,
      (n : ℕ) < (h : ℕ) → heightDistribution n h = 0 := by
  native_decide

/-- Sum a length-ten table. -/
def sumFin10 (f : Fin 10 → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin 10)).sum fun i => f i

/--
Rows are semilength `n = 0, ..., 3`; columns are integer area
`a = 0, ..., 9` under the path.
-/
def areaDistribution : Fin 4 → Fin 10 → ℕ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 2, 1, 1, 1, 0, 0, 0, 0, 0],
    ![1, 3, 3, 3, 4, 3, 2, 1, 1, 1]
  ]

theorem areaDistribution_rows_sum_to_largeSchroeder :
    ∀ n : Fin 4, sumFin10 (areaDistribution n) = largeSchroederFormula n := by
  native_decide

theorem areaDistribution_zero_area_unique :
    ∀ n : Fin 4, areaDistribution n 0 = 1 := by
  native_decide

theorem areaDistribution_support_bound :
    ∀ n : Fin 4, ∀ a : Fin 10,
      (n : ℕ) * (n : ℕ) < (a : ℕ) → areaDistribution n a = 0 := by
  native_decide



structure SchroederPathsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SchroederPathsBudgetCertificate.controlled
    (c : SchroederPathsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SchroederPathsBudgetCertificate.budgetControlled
    (c : SchroederPathsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SchroederPathsBudgetCertificate.Ready
    (c : SchroederPathsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SchroederPathsBudgetCertificate.size
    (c : SchroederPathsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem schroederPaths_budgetCertificate_le_size
    (c : SchroederPathsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSchroederPathsBudgetCertificate :
    SchroederPathsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSchroederPathsBudgetCertificate.Ready := by
  constructor
  · norm_num [SchroederPathsBudgetCertificate.controlled,
      sampleSchroederPathsBudgetCertificate]
  · norm_num [SchroederPathsBudgetCertificate.budgetControlled,
      sampleSchroederPathsBudgetCertificate]

example :
    sampleSchroederPathsBudgetCertificate.certificateBudgetWindow ≤
      sampleSchroederPathsBudgetCertificate.size := by
  apply schroederPaths_budgetCertificate_le_size
  constructor
  · norm_num [SchroederPathsBudgetCertificate.controlled,
      sampleSchroederPathsBudgetCertificate]
  · norm_num [SchroederPathsBudgetCertificate.budgetControlled,
      sampleSchroederPathsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSchroederPathsBudgetCertificate.Ready := by
  constructor
  · norm_num [SchroederPathsBudgetCertificate.controlled,
      sampleSchroederPathsBudgetCertificate]
  · norm_num [SchroederPathsBudgetCertificate.budgetControlled,
      sampleSchroederPathsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSchroederPathsBudgetCertificate.certificateBudgetWindow ≤
      sampleSchroederPathsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SchroederPathsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSchroederPathsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSchroederPathsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.SchroederPaths
