import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.FunctionalEquations2


/-!
  Finite coefficient checks for the functional-equation method in
  analytic combinatorics, Chapter V.

  The series are represented by initial coefficient tables.  The theorems
  below verify the requested identities coefficientwise on the displayed
  ranges.
-/

/-- Lookup in a finite natural-number coefficient table, extended by zero. -/
def coeffNat {N : ℕ} (a : Fin N → ℕ) (n : ℕ) : ℕ :=
  if h : n < N then a ⟨n, h⟩ else 0

/-- Coefficient of `z^n` in the ordinary product of two finite OGF tables. -/
def ogfMulCoeff {N : ℕ} (a b : Fin N → ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => coeffNat a k * coeffNat b (n - k))

/-! ## Catalan equation `C(z) = 1 + z*C(z)^2` -/

/-- Catalan coefficients `C(0)..C(5)`. -/
def catalanCoeffs : Fin 6 → ℕ := ![1, 1, 2, 5, 14, 42]

/-- Coefficient RHS of `1 + z*C(z)^2`. -/
def catalanEquationRHS (n : ℕ) : ℕ :=
  if n = 0 then 1 else ogfMulCoeff catalanCoeffs catalanCoeffs (n - 1)

theorem catalan_functional_equation_up_to_5 :
    ∀ n : Fin 6, coeffNat catalanCoeffs n = catalanEquationRHS n := by
  native_decide

theorem catalan_initial_coefficients :
    coeffNat catalanCoeffs 0 = 1 ∧ coeffNat catalanCoeffs 1 = 1 ∧
    coeffNat catalanCoeffs 2 = 2 ∧ coeffNat catalanCoeffs 3 = 5 := by
  native_decide

/-! ## Motzkin equation `M(z) = 1 + z*M(z) + z^2*M(z)^2` -/

/-- Motzkin coefficients `M(0)..M(5)`. -/
def motzkinCoeffs : Fin 6 → ℕ := ![1, 1, 2, 4, 9, 21]

/-- Coefficient RHS of `1 + z*M(z) + z^2*M(z)^2`. -/
def motzkinEquationRHS (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    coeffNat motzkinCoeffs (n - 1) +
      if n < 2 then 0 else ogfMulCoeff motzkinCoeffs motzkinCoeffs (n - 2)

theorem motzkin_functional_equation_up_to_5 :
    ∀ n : Fin 6, coeffNat motzkinCoeffs n = motzkinEquationRHS n := by
  native_decide

theorem motzkin_initial_coefficients :
    coeffNat motzkinCoeffs 0 = 1 ∧ coeffNat motzkinCoeffs 1 = 1 ∧
    coeffNat motzkinCoeffs 2 = 2 ∧ coeffNat motzkinCoeffs 3 = 4 ∧
    coeffNat motzkinCoeffs 4 = 9 ∧ coeffNat motzkinCoeffs 5 = 21 := by
  native_decide

/-! ## General plane-tree equation `T(z) = z/(1 - T(z))` -/

/-- Plane-tree coefficients for `T(z) = z/(1 - T(z))`, `T(0)..T(5)`. -/
def treeCoeffs : Fin 6 → ℕ := ![0, 1, 1, 2, 5, 14]

/-- Coefficients of `1/(1 - T(z))`; these are shifted Catalan numbers. -/
def treeSeqCoeffs : Fin 6 → ℕ := ![1, 1, 2, 5, 14, 42]

/-- Coefficient RHS of `z/(1 - T(z))`. -/
def treeEquationRHS (n : ℕ) : ℕ :=
  if n = 0 then 0 else coeffNat treeSeqCoeffs (n - 1)

/-- Coefficient RHS of `1 + T(z)/(1 - T(z))` for `1/(1 - T(z))`. -/
def treeSeqEquationRHS (n : ℕ) : ℕ :=
  if n = 0 then 1 else ogfMulCoeff treeCoeffs treeSeqCoeffs n

theorem tree_functional_equation_up_to_5 :
    ∀ n : Fin 6, coeffNat treeCoeffs n = treeEquationRHS n := by
  native_decide

theorem tree_geometric_series_equation_up_to_5 :
    ∀ n : Fin 6, coeffNat treeSeqCoeffs n = treeSeqEquationRHS n := by
  native_decide

theorem tree_initial_coefficients :
    coeffNat treeCoeffs 0 = 0 ∧ coeffNat treeCoeffs 1 = 1 ∧
    coeffNat treeCoeffs 2 = 1 ∧ coeffNat treeCoeffs 3 = 2 ∧
    coeffNat treeCoeffs 4 = 5 ∧ coeffNat treeCoeffs 5 = 14 := by
  native_decide

/-! ## Bell EGF `B(z) = exp(e^z - 1)` -/

/-- Bell numbers `B_0..B_6`. -/
def bellNumbers : Fin 7 → ℕ := ![1, 1, 2, 5, 15, 52, 203]

/-- EGF coefficient `[z^n] B(z) = B_n / n!`, represented as a rational. -/
def bellEgfCoeff (n : ℕ) : ℚ :=
  (coeffNat bellNumbers n : ℚ) / (Nat.factorial n : ℚ)

/-- Extract the Bell number by multiplying the EGF coefficient by `n!`. -/
def bellExtractedCoeff (n : ℕ) : ℚ :=
  bellEgfCoeff n * (Nat.factorial n : ℚ)

theorem bell_egf_coefficient_extraction_up_to_6 :
    ∀ n : Fin 7, bellExtractedCoeff n = (coeffNat bellNumbers n : ℚ) := by
  native_decide

/-- Coefficient recurrence from `B'(z) = e^z * B(z)`, equivalent to
    `B(z) = exp(e^z - 1)` with `B(0)=1`. -/
def bellDerivativeRHS (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => Nat.choose n k * coeffNat bellNumbers k)

theorem bell_exp_exp_minus_one_coefficients_up_to_5 :
    ∀ n : Fin 6, coeffNat bellNumbers (n + 1) = bellDerivativeRHS n := by
  native_decide

/-! ## Schroeder equation `S(z) = 1 + z*S(z) + z*S(z)^2` -/

/-- Large Schroeder coefficients `S(0)..S(5)`. -/
def schroederCoeffs : Fin 6 → ℕ := ![1, 2, 6, 22, 90, 394]

/-- Coefficient RHS of `1 + z*S(z) + z*S(z)^2`. -/
def schroederEquationRHS (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    coeffNat schroederCoeffs (n - 1) +
      ogfMulCoeff schroederCoeffs schroederCoeffs (n - 1)

theorem schroeder_functional_equation_up_to_5 :
    ∀ n : Fin 6, coeffNat schroederCoeffs n = schroederEquationRHS n := by
  native_decide

theorem schroeder_initial_coefficients :
    coeffNat schroederCoeffs 0 = 1 ∧ coeffNat schroederCoeffs 1 = 2 ∧
    coeffNat schroederCoeffs 2 = 6 ∧ coeffNat schroederCoeffs 3 = 22 := by
  native_decide

/-! ## Compositional inverse coefficients -/

/-- Lookup in a finite integer coefficient table, extended by zero. -/
def coeffInt {N : ℕ} (a : Fin N → ℤ) (n : ℕ) : ℤ :=
  if h : n < N then a ⟨n, h⟩ else 0

/-- Coefficient of `z^n` in the product of two integer series. -/
def seriesMulCoeff (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum (fun k => a k * b (n - k))

/-- Coefficient of `z^n` in the `m`-th power of an integer series. -/
def seriesPowCoeff (a : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | m + 1, n =>
      (Finset.range (n + 1)).sum (fun k => seriesPowCoeff a m k * a (n - k))

/-- Coefficient of `z^n` in `f(g(z))`, truncated to terms `f_0..f_n`. -/
def composeCoeff (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum (fun k => f k * seriesPowCoeff g k n)

/-- The identity series `z`. -/
def identityCoeff (n : ℕ) : ℤ :=
  if n = 1 then 1 else 0

/-- Finite predicate for `f(g(z)) = z`. -/
def IsCompositionalInverseUpTo (N : ℕ) (f g : ℕ → ℤ) : Prop :=
  ∀ n : Fin N, composeCoeff f g n = identityCoeff n

/-- Example input coefficients for `f(z) = z - z^2`. -/
def inverseFTable : Fin 7 → ℤ := ![0, 1, -1, 0, 0, 0, 0]

/-- Coefficients of the inverse `g(z) = z + z^2 + 2z^3 + 5z^4 + ...`. -/
def inverseGTable : Fin 7 → ℤ := ![0, 1, 1, 2, 5, 14, 42]

def inverseF (n : ℕ) : ℤ := coeffInt inverseFTable n

def inverseG (n : ℕ) : ℤ := coeffInt inverseGTable n

/-- Recursive coefficient extraction from `f(g(z)) = z` when `f_1 = 1`. -/
def inverseCoeffFromEquation (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n = 0 then
    0
  else if n = 1 then
    1
  else
    -((Finset.range (n + 1)).sum
        (fun k => if k < 2 then 0 else f k * seriesPowCoeff g k n))

theorem inverse_example_composition_up_to_6 :
    ∀ n : Fin 7, composeCoeff inverseF inverseG n = identityCoeff n := by
  native_decide

theorem inverse_coefficients_from_f_coefficients_up_to_6 :
    ∀ n : Fin 7, inverseG n = inverseCoeffFromEquation inverseF inverseG n := by
  native_decide

theorem inverse_example_initial_coefficients :
    inverseG 0 = 0 ∧ inverseG 1 = 1 ∧ inverseG 2 = 1 ∧
    inverseG 3 = 2 ∧ inverseG 4 = 5 ∧ inverseG 5 = 14 ∧
    inverseG 6 = 42 := by
  native_decide



structure FunctionalEquations2BudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FunctionalEquations2BudgetCertificate.controlled
    (c : FunctionalEquations2BudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FunctionalEquations2BudgetCertificate.budgetControlled
    (c : FunctionalEquations2BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FunctionalEquations2BudgetCertificate.Ready
    (c : FunctionalEquations2BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FunctionalEquations2BudgetCertificate.size
    (c : FunctionalEquations2BudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem functionalEquations2_budgetCertificate_le_size
    (c : FunctionalEquations2BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFunctionalEquations2BudgetCertificate :
    FunctionalEquations2BudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFunctionalEquations2BudgetCertificate.Ready := by
  constructor
  · norm_num [FunctionalEquations2BudgetCertificate.controlled,
      sampleFunctionalEquations2BudgetCertificate]
  · norm_num [FunctionalEquations2BudgetCertificate.budgetControlled,
      sampleFunctionalEquations2BudgetCertificate]

example :
    sampleFunctionalEquations2BudgetCertificate.certificateBudgetWindow ≤
      sampleFunctionalEquations2BudgetCertificate.size := by
  apply functionalEquations2_budgetCertificate_le_size
  constructor
  · norm_num [FunctionalEquations2BudgetCertificate.controlled,
      sampleFunctionalEquations2BudgetCertificate]
  · norm_num [FunctionalEquations2BudgetCertificate.budgetControlled,
      sampleFunctionalEquations2BudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFunctionalEquations2BudgetCertificate.Ready := by
  constructor
  · norm_num [FunctionalEquations2BudgetCertificate.controlled,
      sampleFunctionalEquations2BudgetCertificate]
  · norm_num [FunctionalEquations2BudgetCertificate.budgetControlled,
      sampleFunctionalEquations2BudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFunctionalEquations2BudgetCertificate.certificateBudgetWindow ≤
      sampleFunctionalEquations2BudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FunctionalEquations2BudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFunctionalEquations2BudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFunctionalEquations2BudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.FunctionalEquations2
