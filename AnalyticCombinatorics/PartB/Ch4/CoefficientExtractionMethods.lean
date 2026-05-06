import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.CoefficientExtractionMethods


/-!
Methods for extracting coefficients from generating functions, following the
coefficient-extraction examples of Chapter IV of Analytic Combinatorics.
-/

/-! ## Partial fractions for simple rational functions -/

/-- `[z^n] 1 / ((1 - z)(1 - 2z)) = 2^(n+1) - 1`. -/
def oneTwoCoeff (n : ℕ) : ℕ :=
  2 ^ (n + 1) - 1

def oneTwoTable : Fin 9 → ℕ :=
  ![1, 3, 7, 15, 31, 63, 127, 255, 511]

theorem oneTwo_table_closed_form :
    ∀ n : Fin 9, oneTwoTable n = oneTwoCoeff n.val := by native_decide

theorem oneTwo_table_values :
    List.ofFn oneTwoTable = [1, 3, 7, 15, 31, 63, 127, 255, 511] := by native_decide

example : oneTwoCoeff 0 = 1 := by native_decide
example : oneTwoCoeff 1 = 3 := by native_decide
example : oneTwoCoeff 2 = 7 := by native_decide
example : oneTwoCoeff 3 = 15 := by native_decide
example : oneTwoCoeff 4 = 31 := by native_decide
example : oneTwoCoeff 5 = 63 := by native_decide
example : oneTwoCoeff 6 = 127 := by native_decide
example : oneTwoCoeff 7 = 255 := by native_decide
example : oneTwoCoeff 8 = 511 := by native_decide

/-- `[z^n] 1 / ((1 - z)(1 - z)) = n + 1`. -/
def doublePoleCoeff (n : ℕ) : ℕ :=
  n + 1

def doublePoleTable : Fin 9 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9]

theorem doublePole_table_closed_form :
    ∀ n : Fin 9, doublePoleTable n = doublePoleCoeff n.val := by native_decide

theorem doublePole_table_values :
    List.ofFn doublePoleTable = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide

/--
`[z^n] z / ((1 - z)(1 - 2z)(1 - 3z))`.
For `n ≥ 1`, this is `(9 * 3^(n-1) + 1 - 8 * 2^(n-1)) / 2`;
for `n = 0`, the leading factor `z` gives coefficient `0`.
-/
def shiftedOneTwoThreeCoeff (n : ℕ) : ℕ :=
  if n = 0 then
    0
  else
    (9 * 3 ^ (n - 1) + 1 - 8 * 2 ^ (n - 1)) / 2

def shiftedOneTwoThreeTable : Fin 9 → ℕ :=
  ![0, 1, 6, 25, 90, 301, 966, 3025, 9330]

theorem shiftedOneTwoThree_table_closed_form :
    ∀ n : Fin 9, shiftedOneTwoThreeTable n = shiftedOneTwoThreeCoeff n.val := by native_decide

theorem shiftedOneTwoThree_table_values :
    List.ofFn shiftedOneTwoThreeTable = [0, 1, 6, 25, 90, 301, 966, 3025, 9330] := by native_decide

example : shiftedOneTwoThreeCoeff 0 = 0 := by native_decide
example : shiftedOneTwoThreeCoeff 1 = 1 := by native_decide
example : shiftedOneTwoThreeCoeff 2 = 6 := by native_decide
example : shiftedOneTwoThreeCoeff 3 = 25 := by native_decide
example : shiftedOneTwoThreeCoeff 4 = 90 := by native_decide
example : shiftedOneTwoThreeCoeff 5 = 301 := by native_decide
example : shiftedOneTwoThreeCoeff 6 = 966 := by native_decide
example : shiftedOneTwoThreeCoeff 7 = 3025 := by native_decide
example : shiftedOneTwoThreeCoeff 8 = 9330 := by native_decide

/-! ## Recurrence sequences from rational generating functions -/

/-- Coefficients of `z / (1 - z - z^2)`. -/
def fibonacciCoeff : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacciCoeff (n + 1) + fibonacciCoeff n

def fibonacciTable : Fin 11 → ℕ :=
  ![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]

theorem fibonacci_table_closed_form :
    ∀ n : Fin 11, fibonacciTable n = fibonacciCoeff n.val := by native_decide

theorem fibonacci_table_values :
    List.ofFn fibonacciTable = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55] := by native_decide

/-- Tribonacci sequence with `T(0)=0`, `T(1)=0`, `T(2)=1`. -/
def tribonacciCoeff : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => tribonacciCoeff (n + 2) + tribonacciCoeff (n + 1) + tribonacciCoeff n

def tribonacciTable : Fin 10 → ℕ :=
  ![0, 0, 1, 1, 2, 4, 7, 13, 24, 44]

theorem tribonacci_table_closed_form :
    ∀ n : Fin 10, tribonacciTable n = tribonacciCoeff n.val := by native_decide

theorem tribonacci_table_values :
    List.ofFn tribonacciTable = [0, 0, 1, 1, 2, 4, 7, 13, 24, 44] := by native_decide

/-- Lucas sequence with `L(0)=2`, `L(1)=1`. -/
def lucasCoeff : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucasCoeff (n + 1) + lucasCoeff n

def lucasTable : Fin 10 → ℕ :=
  ![2, 1, 3, 4, 7, 11, 18, 29, 47, 76]

theorem lucas_table_closed_form :
    ∀ n : Fin 10, lucasTable n = lucasCoeff n.val := by native_decide

theorem lucas_table_values :
    List.ofFn lucasTable = [2, 1, 3, 4, 7, 11, 18, 29, 47, 76] := by native_decide

theorem lucas_fibonacci_relation_1_to_8 :
    ∀ n : Fin 8, lucasCoeff (n.val + 1) =
      fibonacciCoeff n.val + fibonacciCoeff (n.val + 2) := by native_decide

example : lucasCoeff 1 = fibonacciCoeff 0 + fibonacciCoeff 2 := by native_decide
example : lucasCoeff 2 = fibonacciCoeff 1 + fibonacciCoeff 3 := by native_decide
example : lucasCoeff 3 = fibonacciCoeff 2 + fibonacciCoeff 4 := by native_decide
example : lucasCoeff 4 = fibonacciCoeff 3 + fibonacciCoeff 5 := by native_decide
example : lucasCoeff 5 = fibonacciCoeff 4 + fibonacciCoeff 6 := by native_decide
example : lucasCoeff 6 = fibonacciCoeff 5 + fibonacciCoeff 7 := by native_decide
example : lucasCoeff 7 = fibonacciCoeff 6 + fibonacciCoeff 8 := by native_decide
example : lucasCoeff 8 = fibonacciCoeff 7 + fibonacciCoeff 9 := by native_decide

/-! ## Powers of the geometric generating function -/

/-- `[z^n] (1 / (1 - z))^k = Nat.choose (n + k - 1) (k - 1)` for positive `k`. -/
def geometricPowerCoeff (k n : ℕ) : ℕ :=
  Nat.choose (n + k - 1) (k - 1)

def geometricPowerK1 : Fin 6 → ℕ :=
  ![1, 1, 1, 1, 1, 1]

def geometricPowerK2 : Fin 6 → ℕ :=
  ![1, 2, 3, 4, 5, 6]

def geometricPowerK3 : Fin 6 → ℕ :=
  ![1, 3, 6, 10, 15, 21]

def geometricPowerK4 : Fin 6 → ℕ :=
  ![1, 4, 10, 20, 35, 56]

def geometricPowerK5 : Fin 6 → ℕ :=
  ![1, 5, 15, 35, 70, 126]

theorem geometricPowerK1_closed_form :
    ∀ n : Fin 6, geometricPowerK1 n = geometricPowerCoeff 1 n.val := by native_decide

theorem geometricPowerK2_closed_form :
    ∀ n : Fin 6, geometricPowerK2 n = geometricPowerCoeff 2 n.val := by native_decide

theorem geometricPowerK3_closed_form :
    ∀ n : Fin 6, geometricPowerK3 n = geometricPowerCoeff 3 n.val := by native_decide

theorem geometricPowerK4_closed_form :
    ∀ n : Fin 6, geometricPowerK4 n = geometricPowerCoeff 4 n.val := by native_decide

theorem geometricPowerK5_closed_form :
    ∀ n : Fin 6, geometricPowerK5 n = geometricPowerCoeff 5 n.val := by native_decide

theorem geometricPowerK1_values :
    List.ofFn geometricPowerK1 = [1, 1, 1, 1, 1, 1] := by native_decide

theorem geometricPowerK2_values :
    List.ofFn geometricPowerK2 = [1, 2, 3, 4, 5, 6] := by native_decide

theorem geometricPowerK3_values :
    List.ofFn geometricPowerK3 = [1, 3, 6, 10, 15, 21] := by native_decide

theorem geometricPowerK4_values :
    List.ofFn geometricPowerK4 = [1, 4, 10, 20, 35, 56] := by native_decide

theorem geometricPowerK5_values :
    List.ofFn geometricPowerK5 = [1, 5, 15, 35, 70, 126] := by native_decide



structure CoefficientExtractionMethodsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoefficientExtractionMethodsBudgetCertificate.controlled
    (c : CoefficientExtractionMethodsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CoefficientExtractionMethodsBudgetCertificate.budgetControlled
    (c : CoefficientExtractionMethodsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CoefficientExtractionMethodsBudgetCertificate.Ready
    (c : CoefficientExtractionMethodsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CoefficientExtractionMethodsBudgetCertificate.size
    (c : CoefficientExtractionMethodsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem coefficientExtractionMethods_budgetCertificate_le_size
    (c : CoefficientExtractionMethodsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCoefficientExtractionMethodsBudgetCertificate :
    CoefficientExtractionMethodsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCoefficientExtractionMethodsBudgetCertificate.Ready := by
  constructor
  · norm_num [CoefficientExtractionMethodsBudgetCertificate.controlled,
      sampleCoefficientExtractionMethodsBudgetCertificate]
  · norm_num [CoefficientExtractionMethodsBudgetCertificate.budgetControlled,
      sampleCoefficientExtractionMethodsBudgetCertificate]

example :
    sampleCoefficientExtractionMethodsBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientExtractionMethodsBudgetCertificate.size := by
  apply coefficientExtractionMethods_budgetCertificate_le_size
  constructor
  · norm_num [CoefficientExtractionMethodsBudgetCertificate.controlled,
      sampleCoefficientExtractionMethodsBudgetCertificate]
  · norm_num [CoefficientExtractionMethodsBudgetCertificate.budgetControlled,
      sampleCoefficientExtractionMethodsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCoefficientExtractionMethodsBudgetCertificate.Ready := by
  constructor
  · norm_num [CoefficientExtractionMethodsBudgetCertificate.controlled,
      sampleCoefficientExtractionMethodsBudgetCertificate]
  · norm_num [CoefficientExtractionMethodsBudgetCertificate.budgetControlled,
      sampleCoefficientExtractionMethodsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCoefficientExtractionMethodsBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientExtractionMethodsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CoefficientExtractionMethodsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCoefficientExtractionMethodsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCoefficientExtractionMethodsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.CoefficientExtractionMethods
