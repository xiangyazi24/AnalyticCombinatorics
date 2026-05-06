import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.MultiplicativeFunctions


/-!
Bounded coefficient tables for multiplicative arithmetic functions and
Dirichlet-series examples from Chapter VI.
-/

def jordanTwoTable : Fin 12 → ℕ :=
  ![1, 3, 8, 12, 24, 24, 48, 48, 72, 72, 120, 96]

def jordanThreeTable : Fin 12 → ℕ :=
  ![1, 7, 26, 56, 124, 182, 342, 448, 702, 868, 1330, 1456]

def sigmaTwoTable : Fin 12 → ℕ :=
  ![1, 5, 10, 21, 26, 50, 50, 85, 91, 130, 122, 210]

def sigmaThreeTable : Fin 12 → ℕ :=
  ![1, 9, 28, 73, 126, 252, 344, 585, 757, 1134, 1332, 2044]

def ramanujanTauTable : Fin 12 → ℤ :=
  ![1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612,
    -370944]

def unitaryDivisorCountTable : Fin 12 → ℕ :=
  ![1, 2, 2, 2, 2, 4, 2, 2, 2, 4, 2, 4]

def unitaryDivisorSumTable : Fin 12 → ℕ :=
  ![1, 3, 4, 5, 6, 12, 8, 9, 10, 18, 12, 20]

def squareFreeIndicatorTable : Fin 12 → ℕ :=
  ![1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0]

def squareFreeCountingTable : Fin 12 → ℕ :=
  ![1, 2, 3, 3, 4, 5, 6, 6, 6, 7, 8, 8]

def powerfulIndicatorTable : Fin 12 → ℕ :=
  ![1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0]

def powerfulCountingTable : Fin 12 → ℕ :=
  ![1, 1, 1, 2, 2, 2, 2, 3, 4, 4, 4, 4]

def twoSquaresRepresentationTable : Fin 12 → ℕ :=
  ![4, 4, 0, 4, 8, 0, 0, 4, 4, 8, 0, 0]

def jordanTwo : ℕ → ℕ
  | 1 => 1
  | 2 => 3
  | 3 => 8
  | 4 => 12
  | 5 => 24
  | 6 => 24
  | 7 => 48
  | 8 => 48
  | 9 => 72
  | 10 => 72
  | 11 => 120
  | 12 => 96
  | _ => 0

def sigmaTwo : ℕ → ℕ
  | 1 => 1
  | 2 => 5
  | 3 => 10
  | 4 => 21
  | 5 => 26
  | 6 => 50
  | 7 => 50
  | 8 => 85
  | 9 => 91
  | 10 => 130
  | 11 => 122
  | 12 => 210
  | _ => 0

def ramanujanTau : ℕ → ℤ
  | 1 => 1
  | 2 => -24
  | 3 => 252
  | 4 => -1472
  | 5 => 4830
  | 6 => -6048
  | 7 => -16744
  | 8 => 84480
  | 9 => -113643
  | 10 => -115920
  | 11 => 534612
  | 12 => -370944
  | _ => 0

def unitaryDivisorSum : ℕ → ℕ
  | 1 => 1
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 12
  | 7 => 8
  | 8 => 9
  | 9 => 10
  | 10 => 18
  | 11 => 12
  | 12 => 20
  | _ => 0

def squareFreeIndicator : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 0
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => 1
  | 12 => 0
  | _ => 0

def divisorSumNat (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl
    (fun acc d => if d ≠ 0 ∧ n % d = 0 then acc + f d else acc) 0

def partialSumNat (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range n).foldl (fun acc i => acc + f (i + 1)) 0

theorem jordan_two_table_values :
    jordanTwoTable 0 = 1 ∧ jordanTwoTable 1 = 3 ∧ jordanTwoTable 2 = 8 ∧
      jordanTwoTable 3 = 12 ∧ jordanTwoTable 4 = 24 ∧ jordanTwoTable 5 = 24 ∧
      jordanTwoTable 6 = 48 ∧ jordanTwoTable 7 = 48 ∧ jordanTwoTable 8 = 72 ∧
      jordanTwoTable 9 = 72 ∧ jordanTwoTable 10 = 120 ∧ jordanTwoTable 11 = 96 := by
  native_decide

theorem jordan_three_table_values :
    jordanThreeTable 0 = 1 ∧ jordanThreeTable 1 = 7 ∧ jordanThreeTable 2 = 26 ∧
      jordanThreeTable 3 = 56 ∧ jordanThreeTable 4 = 124 ∧ jordanThreeTable 5 = 182 ∧
      jordanThreeTable 6 = 342 ∧ jordanThreeTable 7 = 448 ∧
      jordanThreeTable 8 = 702 ∧ jordanThreeTable 9 = 868 ∧
      jordanThreeTable 10 = 1330 ∧ jordanThreeTable 11 = 1456 := by
  native_decide

theorem sigma_two_table_values :
    sigmaTwoTable 0 = 1 ∧ sigmaTwoTable 1 = 5 ∧ sigmaTwoTable 2 = 10 ∧
      sigmaTwoTable 3 = 21 ∧ sigmaTwoTable 4 = 26 ∧ sigmaTwoTable 5 = 50 ∧
      sigmaTwoTable 6 = 50 ∧ sigmaTwoTable 7 = 85 ∧ sigmaTwoTable 8 = 91 ∧
      sigmaTwoTable 9 = 130 ∧ sigmaTwoTable 10 = 122 ∧ sigmaTwoTable 11 = 210 := by
  native_decide

theorem sigma_three_table_values :
    sigmaThreeTable 0 = 1 ∧ sigmaThreeTable 1 = 9 ∧ sigmaThreeTable 2 = 28 ∧
      sigmaThreeTable 3 = 73 ∧ sigmaThreeTable 4 = 126 ∧ sigmaThreeTable 5 = 252 ∧
      sigmaThreeTable 6 = 344 ∧ sigmaThreeTable 7 = 585 ∧
      sigmaThreeTable 8 = 757 ∧ sigmaThreeTable 9 = 1134 ∧
      sigmaThreeTable 10 = 1332 ∧ sigmaThreeTable 11 = 2044 := by
  native_decide

theorem tau_table_values :
    ramanujanTauTable 0 = 1 ∧ ramanujanTauTable 1 = -24 ∧
      ramanujanTauTable 2 = 252 ∧ ramanujanTauTable 3 = -1472 ∧
      ramanujanTauTable 4 = 4830 ∧ ramanujanTauTable 5 = -6048 ∧
      ramanujanTauTable 6 = -16744 ∧ ramanujanTauTable 7 = 84480 ∧
      ramanujanTauTable 8 = -113643 ∧ ramanujanTauTable 9 = -115920 ∧
      ramanujanTauTable 10 = 534612 ∧ ramanujanTauTable 11 = -370944 := by
  native_decide

theorem tau_multiplicative_sample :
    ramanujanTau 6 = ramanujanTau 2 * ramanujanTau 3 ∧
      ramanujanTau 10 = ramanujanTau 2 * ramanujanTau 5 ∧
      ramanujanTau 12 = ramanujanTau 3 * ramanujanTau 4 := by
  native_decide

theorem unitary_divisor_tables :
    unitaryDivisorCountTable 0 = 1 ∧ unitaryDivisorCountTable 5 = 4 ∧
      unitaryDivisorCountTable 11 = 4 ∧ unitaryDivisorSumTable 0 = 1 ∧
      unitaryDivisorSumTable 3 = 5 ∧ unitaryDivisorSumTable 5 = 12 ∧
      unitaryDivisorSumTable 11 = 20 := by
  native_decide

theorem square_free_tables :
    squareFreeIndicatorTable 0 = 1 ∧ squareFreeIndicatorTable 3 = 0 ∧
      squareFreeIndicatorTable 5 = 1 ∧ squareFreeIndicatorTable 8 = 0 ∧
      squareFreeCountingTable 0 = 1 ∧ squareFreeCountingTable 5 = 5 ∧
      squareFreeCountingTable 11 = 8 := by
  native_decide

theorem powerful_number_tables :
    powerfulIndicatorTable 0 = 1 ∧ powerfulIndicatorTable 3 = 1 ∧
      powerfulIndicatorTable 7 = 1 ∧ powerfulIndicatorTable 8 = 1 ∧
      powerfulCountingTable 0 = 1 ∧ powerfulCountingTable 7 = 3 ∧
      powerfulCountingTable 11 = 4 := by
  native_decide

theorem two_squares_table_values :
    twoSquaresRepresentationTable 0 = 4 ∧ twoSquaresRepresentationTable 1 = 4 ∧
      twoSquaresRepresentationTable 2 = 0 ∧ twoSquaresRepresentationTable 3 = 4 ∧
      twoSquaresRepresentationTable 4 = 8 ∧ twoSquaresRepresentationTable 7 = 4 ∧
      twoSquaresRepresentationTable 8 = 4 ∧ twoSquaresRepresentationTable 9 = 8 ∧
      twoSquaresRepresentationTable 11 = 0 := by
  native_decide

theorem sigma_two_as_divisor_sum :
    divisorSumNat (fun d => d ^ 2) 1 = sigmaTwo 1 ∧
      divisorSumNat (fun d => d ^ 2) 2 = sigmaTwo 2 ∧
      divisorSumNat (fun d => d ^ 2) 3 = sigmaTwo 3 ∧
      divisorSumNat (fun d => d ^ 2) 4 = sigmaTwo 4 ∧
      divisorSumNat (fun d => d ^ 2) 5 = sigmaTwo 5 ∧
      divisorSumNat (fun d => d ^ 2) 6 = sigmaTwo 6 ∧
      divisorSumNat (fun d => d ^ 2) 7 = sigmaTwo 7 ∧
      divisorSumNat (fun d => d ^ 2) 8 = sigmaTwo 8 ∧
      divisorSumNat (fun d => d ^ 2) 9 = sigmaTwo 9 ∧
      divisorSumNat (fun d => d ^ 2) 10 = sigmaTwo 10 ∧
      divisorSumNat (fun d => d ^ 2) 11 = sigmaTwo 11 ∧
      divisorSumNat (fun d => d ^ 2) 12 = sigmaTwo 12 := by
  native_decide

theorem square_free_partial_sums :
    partialSumNat squareFreeIndicator 1 = squareFreeCountingTable 0 ∧
      partialSumNat squareFreeIndicator 2 = squareFreeCountingTable 1 ∧
      partialSumNat squareFreeIndicator 3 = squareFreeCountingTable 2 ∧
      partialSumNat squareFreeIndicator 4 = squareFreeCountingTable 3 ∧
      partialSumNat squareFreeIndicator 5 = squareFreeCountingTable 4 ∧
      partialSumNat squareFreeIndicator 6 = squareFreeCountingTable 5 ∧
      partialSumNat squareFreeIndicator 7 = squareFreeCountingTable 6 ∧
      partialSumNat squareFreeIndicator 8 = squareFreeCountingTable 7 ∧
      partialSumNat squareFreeIndicator 9 = squareFreeCountingTable 8 ∧
      partialSumNat squareFreeIndicator 10 = squareFreeCountingTable 9 ∧
      partialSumNat squareFreeIndicator 11 = squareFreeCountingTable 10 ∧
      partialSumNat squareFreeIndicator 12 = squareFreeCountingTable 11 := by
  native_decide

theorem jordan_two_multiplicative_samples :
    jordanTwo 6 = jordanTwo 2 * jordanTwo 3 ∧
      jordanTwo 10 = jordanTwo 2 * jordanTwo 5 ∧
      jordanTwo 12 = jordanTwo 3 * jordanTwo 4 := by
  native_decide

theorem unitary_sum_multiplicative_samples :
    unitaryDivisorSum 6 = unitaryDivisorSum 2 * unitaryDivisorSum 3 ∧
      unitaryDivisorSum 10 = unitaryDivisorSum 2 * unitaryDivisorSum 5 ∧
      unitaryDivisorSum 12 = unitaryDivisorSum 3 * unitaryDivisorSum 4 := by
  native_decide



structure MultiplicativeFunctionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultiplicativeFunctionsBudgetCertificate.controlled
    (c : MultiplicativeFunctionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MultiplicativeFunctionsBudgetCertificate.budgetControlled
    (c : MultiplicativeFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MultiplicativeFunctionsBudgetCertificate.Ready
    (c : MultiplicativeFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultiplicativeFunctionsBudgetCertificate.size
    (c : MultiplicativeFunctionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem multiplicativeFunctions_budgetCertificate_le_size
    (c : MultiplicativeFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMultiplicativeFunctionsBudgetCertificate :
    MultiplicativeFunctionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleMultiplicativeFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [MultiplicativeFunctionsBudgetCertificate.controlled,
      sampleMultiplicativeFunctionsBudgetCertificate]
  · norm_num [MultiplicativeFunctionsBudgetCertificate.budgetControlled,
      sampleMultiplicativeFunctionsBudgetCertificate]

example :
    sampleMultiplicativeFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleMultiplicativeFunctionsBudgetCertificate.size := by
  apply multiplicativeFunctions_budgetCertificate_le_size
  constructor
  · norm_num [MultiplicativeFunctionsBudgetCertificate.controlled,
      sampleMultiplicativeFunctionsBudgetCertificate]
  · norm_num [MultiplicativeFunctionsBudgetCertificate.budgetControlled,
      sampleMultiplicativeFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMultiplicativeFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [MultiplicativeFunctionsBudgetCertificate.controlled,
      sampleMultiplicativeFunctionsBudgetCertificate]
  · norm_num [MultiplicativeFunctionsBudgetCertificate.budgetControlled,
      sampleMultiplicativeFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultiplicativeFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleMultiplicativeFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MultiplicativeFunctionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultiplicativeFunctionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMultiplicativeFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.MultiplicativeFunctions
