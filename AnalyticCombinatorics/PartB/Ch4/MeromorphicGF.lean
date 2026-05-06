import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.MeromorphicGF


/-!
Bounded executable checks for meromorphic generating functions, partial
fractions, rational coefficient extraction, and small transfer matrices.
-/

def oneTwoPartialCoeff (n : ℕ) : ℕ :=
  2 ^ (n + 1) - 1

def oneTwoPartialTable : Fin 15 → ℕ :=
  ![1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383, 32767]

theorem oneTwoPartial_table_closed_form :
    ∀ n : Fin 15, oneTwoPartialTable n = oneTwoPartialCoeff n.val := by
  native_decide

theorem oneTwoPartial_convolution_form :
    ∀ n : Fin 15,
      oneTwoPartialTable n = (List.range (n.val + 1)).foldl (fun s k => s + 2 ^ k) 0 := by
  native_decide

def doublePoleTwoCoeff (n : ℕ) : ℕ :=
  (n + 1) * 2 ^ n

def doublePoleTwoTable : Fin 15 → ℕ :=
  ![1, 4, 12, 32, 80, 192, 448, 1024, 2304, 5120, 11264, 24576, 53248, 114688, 245760]

theorem doublePoleTwo_table_closed_form :
    ∀ n : Fin 15, doublePoleTwoTable n = doublePoleTwoCoeff n.val := by
  native_decide

def fibCoeff : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibCoeff (n + 1) + fibCoeff n

def fibTable : Fin 15 → ℕ :=
  ![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377]

theorem fib_table_closed_form :
    ∀ n : Fin 15, fibTable n = fibCoeff n.val := by
  native_decide

theorem fib_characteristic_recurrence :
    ∀ n : Fin 13, fibCoeff (n.val + 2) = fibCoeff (n.val + 1) + fibCoeff n.val := by
  native_decide

def companionStep (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.2, p.1 + p.2)

def companionIter : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => companionStep (companionIter n)

def transferFibCoeff (n : ℕ) : ℕ :=
  (companionIter n).1

theorem fibonacci_transfer_matrix_table :
    ∀ n : Fin 15, fibTable n = transferFibCoeff n.val := by
  native_decide

def rootsOneTwoCoeff (n : ℕ) : ℕ :=
  2 ^ n + 1

def rootsOneTwoTable : Fin 15 → ℕ :=
  ![2, 3, 5, 9, 17, 33, 65, 129, 257, 513, 1025, 2049, 4097, 8193, 16385]

theorem rootsOneTwo_table_closed_form :
    ∀ n : Fin 15, rootsOneTwoTable n = rootsOneTwoCoeff n.val := by
  native_decide

theorem rootsOneTwo_characteristic_recurrence :
    ∀ n : Fin 13,
      rootsOneTwoCoeff (n.val + 2) + 2 * rootsOneTwoCoeff n.val =
        3 * rootsOneTwoCoeff (n.val + 1) := by
  native_decide

def squareNumeratorCoeff (n : ℕ) : ℕ :=
  Nat.choose (n + 2) 2 + if n = 0 then 0 else Nat.choose (n + 1) 2

def squareCoeff (n : ℕ) : ℕ :=
  (n + 1) ^ 2

def squareCoeffTable : Fin 15 → ℕ :=
  ![1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225]

theorem squareCoeff_table_closed_form :
    ∀ n : Fin 15, squareCoeffTable n = squareCoeff n.val := by
  native_decide

theorem squareCoeff_rational_extraction :
    ∀ n : Fin 15, squareNumeratorCoeff n.val = squareCoeff n.val := by
  native_decide

def thirdOrderRationalCoeff : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | n + 3 =>
      6 * thirdOrderRationalCoeff (n + 2) -
        11 * thirdOrderRationalCoeff (n + 1) +
          6 * thirdOrderRationalCoeff n

def thirdOrderRationalTable : Fin 15 → ℕ :=
  ![1, 2, 5, 14, 41, 122, 365, 1094, 3281, 9842, 29525, 88574, 265721, 797162, 2391485]

theorem thirdOrderRational_table_closed_form :
    ∀ n : Fin 15, thirdOrderRationalTable n = thirdOrderRationalCoeff n.val := by
  native_decide

theorem thirdOrderRational_characteristic_recurrence :
    ∀ n : Fin 12,
      thirdOrderRationalCoeff (n.val + 3) +
          11 * thirdOrderRationalCoeff (n.val + 1) =
        6 * thirdOrderRationalCoeff (n.val + 2) +
          6 * thirdOrderRationalCoeff n.val := by
  native_decide



structure MeromorphicGFBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MeromorphicGFBudgetCertificate.controlled
    (c : MeromorphicGFBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MeromorphicGFBudgetCertificate.budgetControlled
    (c : MeromorphicGFBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MeromorphicGFBudgetCertificate.Ready
    (c : MeromorphicGFBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MeromorphicGFBudgetCertificate.size
    (c : MeromorphicGFBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem meromorphicGF_budgetCertificate_le_size
    (c : MeromorphicGFBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMeromorphicGFBudgetCertificate :
    MeromorphicGFBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleMeromorphicGFBudgetCertificate.Ready := by
  constructor
  · norm_num [MeromorphicGFBudgetCertificate.controlled,
      sampleMeromorphicGFBudgetCertificate]
  · norm_num [MeromorphicGFBudgetCertificate.budgetControlled,
      sampleMeromorphicGFBudgetCertificate]

example :
    sampleMeromorphicGFBudgetCertificate.certificateBudgetWindow ≤
      sampleMeromorphicGFBudgetCertificate.size := by
  apply meromorphicGF_budgetCertificate_le_size
  constructor
  · norm_num [MeromorphicGFBudgetCertificate.controlled,
      sampleMeromorphicGFBudgetCertificate]
  · norm_num [MeromorphicGFBudgetCertificate.budgetControlled,
      sampleMeromorphicGFBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMeromorphicGFBudgetCertificate.Ready := by
  constructor
  · norm_num [MeromorphicGFBudgetCertificate.controlled,
      sampleMeromorphicGFBudgetCertificate]
  · norm_num [MeromorphicGFBudgetCertificate.budgetControlled,
      sampleMeromorphicGFBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMeromorphicGFBudgetCertificate.certificateBudgetWindow ≤
      sampleMeromorphicGFBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MeromorphicGFBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMeromorphicGFBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMeromorphicGFBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.MeromorphicGF
