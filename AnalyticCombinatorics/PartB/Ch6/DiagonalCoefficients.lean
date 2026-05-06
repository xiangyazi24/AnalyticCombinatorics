import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.DiagonalCoefficients


/-!
  Finite coefficient tables for diagonals of multivariate generating functions,
  in the spirit of Chapter VI of Flajolet and Sedgewick.

  The file deliberately keeps every computation bounded and verifies only
  concrete table identities.
-/

-- ============================================================
-- Delannoy numbers
-- ============================================================

/-- Delannoy numbers from `(0,0)` to `(m,n)`. -/
def delannoy (m n : ℕ) : ℕ :=
  (Finset.range (Nat.min m n + 1)).sum
    (fun k => Nat.choose m k * Nat.choose n k * 2 ^ k)

/-- Central Delannoy numbers, the main diagonal of `1 / (1 - x - y - x*y)`. -/
def centralDelannoy (n : ℕ) : ℕ :=
  delannoy n n

/-- Central Delannoy values `D(0,0), ..., D(11,11)`. -/
def centralDelannoyTable : Fin 12 → ℕ :=
  ![1, 3, 13, 63, 321, 1683, 8989, 48639, 265729, 1462563, 8097453, 45046719]

/-- The diagonal formula gives the central Delannoy table through `n = 11`. -/
theorem centralDelannoy_values_0_11 :
    ∀ n : Fin 12, centralDelannoy n = centralDelannoyTable n := by native_decide

/-- The row `D(4,n)` for `n = 0, ..., 9`. -/
def delannoyRowFourTable : Fin 10 → ℕ :=
  ![1, 9, 41, 129, 321, 681, 1289, 2241, 3649, 5641]

/-- A fixed off-diagonal row of the Delannoy array. -/
theorem delannoy_row_four_values_0_9 :
    ∀ n : Fin 10, delannoy 4 n = delannoyRowFourTable n := by native_decide

/-- Symmetry of the bounded Delannoy table. -/
theorem delannoy_symmetry_0_7 :
    ∀ m n : Fin 8, delannoy m n = delannoy n m := by native_decide

-- ============================================================
-- Apéry-like and Franel diagonals
-- ============================================================

/-- Apéry numbers `A(n) = sum_k binom(n,k)^2 binom(n+k,k)^2`. -/
def aperyNumber (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum
    (fun k => Nat.choose n k ^ 2 * Nat.choose (n + k) k ^ 2)

/-- Apéry values `A(0), ..., A(5)`. -/
def aperyTable : Fin 6 → ℕ :=
  ![1, 5, 73, 1445, 33001, 819005]

/-- The Apéry diagonal formula gives the first six values. -/
theorem apery_values_0_5 :
    ∀ n : Fin 6, aperyNumber n = aperyTable n := by native_decide

/-- Franel numbers `F(n) = sum_k binom(n,k)^3`. -/
def franelNumber (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum
    (fun k => Nat.choose n k ^ 3)

/-- Franel values `F(0), ..., F(9)`. -/
def franelTable : Fin 10 → ℕ :=
  ![1, 2, 10, 56, 346, 2252, 15184, 104960, 739162, 5280932]

/-- The Franel diagonal formula gives the first ten values. -/
theorem franel_values_0_9 :
    ∀ n : Fin 10, franelNumber n = franelTable n := by native_decide

-- ============================================================
-- Catalan, Narayana, and super Catalan refinements
-- ============================================================

/-- Catalan numbers, used as row sums for Narayana refinements. -/
def catalanCoeff (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Narayana numbers, with zero boundary cases for bounded row sums. -/
def narayanaNumber (n k : ℕ) : ℕ :=
  if n = 0 ∨ k = 0 then
    0
  else
    (Nat.choose n k * Nat.choose n (k - 1)) / n

/-- Sum of the `n`th Narayana row. -/
def narayanaRowSum (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => narayanaNumber n k)

/-- The Narayana row for `n = 5`, indexed by `k = 1, ..., 5`. -/
def narayanaRowFiveTable : Fin 5 → ℕ :=
  ![1, 10, 20, 10, 1]

/-- The `n = 5` Narayana refinement row. -/
theorem narayana_row_five_values :
    ∀ k : Fin 5, narayanaNumber 5 ((k : ℕ) + 1) = narayanaRowFiveTable k := by
  native_decide

/-- Narayana rows sum to Catalan numbers for `n = 1, ..., 8`. -/
theorem narayana_row_sums_eq_catalan_1_8 :
    ∀ n : Fin 8, narayanaRowSum ((n : ℕ) + 1) = catalanCoeff ((n : ℕ) + 1) := by
  native_decide

/-- Super Catalan numbers `S(m,n) = (2m)!(2n)! / (m! n! (m+n)!)`. -/
def superCatalan (m n : ℕ) : ℕ :=
  (Nat.factorial (2 * m) * Nat.factorial (2 * n)) /
    (Nat.factorial m * Nat.factorial n * Nat.factorial (m + n))

/-- The row `S(2,n)` for `n = 0, ..., 9`. -/
def superCatalanRowTwoTable : Fin 10 → ℕ :=
  ![6, 4, 6, 12, 28, 72, 198, 572, 1716, 5304]

/-- A bounded super Catalan row. -/
theorem superCatalan_row_two_values_0_9 :
    ∀ n : Fin 10, superCatalan 2 n = superCatalanRowTwoTable n := by native_decide

/-- On the diagonal, this normalization recovers central binomial coefficients. -/
theorem superCatalan_diagonal_eq_central_binomial_0_9 :
    ∀ n : Fin 10, superCatalan n n = Nat.choose (2 * (n : ℕ)) (n : ℕ) := by
  native_decide

-- ============================================================
-- Central trinomial coefficients
-- ============================================================

/-- Central trinomial coefficients from the diagonal of `(1 + x + x^2)^n`. -/
def centralTrinomial (n : ℕ) : ℕ :=
  (Finset.range (n / 2 + 1)).sum
    (fun k => Nat.choose n (2 * k) * Nat.choose (2 * k) k)

/-- Central trinomial values `T(0), ..., T(11)`. -/
def centralTrinomialTable : Fin 12 → ℕ :=
  ![1, 1, 3, 7, 19, 51, 141, 393, 1107, 3139, 8953, 25653]

/-- The central trinomial formula gives the first twelve values. -/
theorem centralTrinomial_values_0_11 :
    ∀ n : Fin 12, centralTrinomial n = centralTrinomialTable n := by native_decide

/-- The standard three-term recurrence holds for `T(2), ..., T(11)`. -/
theorem centralTrinomial_recurrence_2_11 :
    ∀ i : Fin 10,
      let n := (i : ℕ) + 2
      n * centralTrinomial n =
        (2 * n - 1) * centralTrinomial (n - 1) +
          3 * (n - 1) * centralTrinomial (n - 2) := by
  native_decide



structure DiagonalCoefficientsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DiagonalCoefficientsBudgetCertificate.controlled
    (c : DiagonalCoefficientsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DiagonalCoefficientsBudgetCertificate.budgetControlled
    (c : DiagonalCoefficientsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DiagonalCoefficientsBudgetCertificate.Ready
    (c : DiagonalCoefficientsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DiagonalCoefficientsBudgetCertificate.size
    (c : DiagonalCoefficientsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem diagonalCoefficients_budgetCertificate_le_size
    (c : DiagonalCoefficientsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDiagonalCoefficientsBudgetCertificate :
    DiagonalCoefficientsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleDiagonalCoefficientsBudgetCertificate.Ready := by
  constructor
  · norm_num [DiagonalCoefficientsBudgetCertificate.controlled,
      sampleDiagonalCoefficientsBudgetCertificate]
  · norm_num [DiagonalCoefficientsBudgetCertificate.budgetControlled,
      sampleDiagonalCoefficientsBudgetCertificate]

example :
    sampleDiagonalCoefficientsBudgetCertificate.certificateBudgetWindow ≤
      sampleDiagonalCoefficientsBudgetCertificate.size := by
  apply diagonalCoefficients_budgetCertificate_le_size
  constructor
  · norm_num [DiagonalCoefficientsBudgetCertificate.controlled,
      sampleDiagonalCoefficientsBudgetCertificate]
  · norm_num [DiagonalCoefficientsBudgetCertificate.budgetControlled,
      sampleDiagonalCoefficientsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDiagonalCoefficientsBudgetCertificate.Ready := by
  constructor
  · norm_num [DiagonalCoefficientsBudgetCertificate.controlled,
      sampleDiagonalCoefficientsBudgetCertificate]
  · norm_num [DiagonalCoefficientsBudgetCertificate.budgetControlled,
      sampleDiagonalCoefficientsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDiagonalCoefficientsBudgetCertificate.certificateBudgetWindow ≤
      sampleDiagonalCoefficientsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DiagonalCoefficientsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDiagonalCoefficientsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDiagonalCoefficientsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.DiagonalCoefficients
