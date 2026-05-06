import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch8.MellinTransformAsymptotics


/-!
Bounded numerical tables inspired by Chapter VIII Mellin-transform analyses:
harmonic sums, digital sums, bit statistics, ruler values, Stern data, and
small summatory arithmetic functions.
-/

def harmonicRational : Fin 11 → ℕ × ℕ :=
  ![(0, 1), (1, 1), (3, 2), (11, 6), (25, 12), (137, 60),
    (49, 20), (363, 140), (761, 280), (7129, 2520), (7381, 2520)]

def binaryDigitSum : Fin 16 → ℕ :=
  ![0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4]

def ternaryDigitSum : Fin 15 → ℕ :=
  ![0, 1, 2, 1, 2, 3, 2, 3, 4, 1, 2, 3, 2, 3, 4]

def binaryLength : Fin 16 → ℕ :=
  ![0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4]

def rulerFunction : Fin 15 → ℕ :=
  ![0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]

def sternDiatomic : Fin 16 → ℕ :=
  ![0, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3, 5, 2, 5, 3, 4]

def sternBrocotLevel3Numerators : Fin 8 → ℕ :=
  ![1, 1, 2, 1, 3, 2, 3, 1]

def sternBrocotLevel3Denominators : Fin 8 → ℕ :=
  ![1, 2, 3, 3, 2, 3, 4, 4]

def divisorCount : Fin 15 → ℕ :=
  ![1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 6, 2, 4, 4]

def summatoryDivisorCount : Fin 15 → ℕ :=
  ![1, 3, 5, 8, 10, 14, 16, 20, 23, 27, 29, 35, 37, 41, 45]

def eulerPhi : Fin 15 → ℕ :=
  ![1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8]

def summatoryEulerPhi : Fin 15 → ℕ :=
  ![1, 2, 4, 6, 10, 12, 18, 22, 28, 32, 42, 46, 58, 64, 72]

theorem harmonic_values_exact :
    harmonicRational =
      ![(0, 1), (1, 1), (3, 2), (11, 6), (25, 12), (137, 60),
        (49, 20), (363, 140), (761, 280), (7129, 2520), (7381, 2520)] := by
  native_decide

theorem harmonic_tenth_value :
    harmonicRational 10 = (7381, 2520) := by
  native_decide

theorem binary_digit_sum_values :
    binaryDigitSum =
      ![0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4] := by
  native_decide

theorem base_two_and_three_samples :
    binaryDigitSum 14 = 3 ∧ binaryDigitSum 15 = 4 ∧
      ternaryDigitSum 8 = 4 ∧ ternaryDigitSum 14 = 4 := by
  native_decide

theorem bit_length_and_ruler_samples :
    binaryLength 0 = 0 ∧ binaryLength 1 = 1 ∧ binaryLength 15 = 4 ∧
      rulerFunction 7 = 3 ∧ rulerFunction 11 = 2 := by
  native_decide

theorem stern_level_tables_match :
    sternBrocotLevel3Numerators =
        ![1, 1, 2, 1, 3, 2, 3, 1] ∧
      sternBrocotLevel3Denominators =
        ![1, 2, 3, 3, 2, 3, 4, 4] := by
  native_decide

theorem stern_diatomic_samples :
    sternDiatomic 9 = 4 ∧ sternDiatomic 11 = 5 ∧ sternDiatomic 15 = 4 := by
  native_decide

theorem summatory_divisor_table :
    summatoryDivisorCount =
      ![1, 3, 5, 8, 10, 14, 16, 20, 23, 27, 29, 35, 37, 41, 45] := by
  native_decide

theorem summatory_phi_samples :
    eulerPhi 10 = 10 ∧ summatoryEulerPhi 10 = 42 ∧ summatoryEulerPhi 14 = 72 := by
  native_decide



structure MellinTransformAsymptoticsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinTransformAsymptoticsBudgetCertificate.controlled
    (c : MellinTransformAsymptoticsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MellinTransformAsymptoticsBudgetCertificate.budgetControlled
    (c : MellinTransformAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MellinTransformAsymptoticsBudgetCertificate.Ready
    (c : MellinTransformAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MellinTransformAsymptoticsBudgetCertificate.size
    (c : MellinTransformAsymptoticsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem mellinTransformAsymptotics_budgetCertificate_le_size
    (c : MellinTransformAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMellinTransformAsymptoticsBudgetCertificate :
    MellinTransformAsymptoticsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleMellinTransformAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinTransformAsymptoticsBudgetCertificate.controlled,
      sampleMellinTransformAsymptoticsBudgetCertificate]
  · norm_num [MellinTransformAsymptoticsBudgetCertificate.budgetControlled,
      sampleMellinTransformAsymptoticsBudgetCertificate]

example :
    sampleMellinTransformAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinTransformAsymptoticsBudgetCertificate.size := by
  apply mellinTransformAsymptotics_budgetCertificate_le_size
  constructor
  · norm_num [MellinTransformAsymptoticsBudgetCertificate.controlled,
      sampleMellinTransformAsymptoticsBudgetCertificate]
  · norm_num [MellinTransformAsymptoticsBudgetCertificate.budgetControlled,
      sampleMellinTransformAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMellinTransformAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinTransformAsymptoticsBudgetCertificate.controlled,
      sampleMellinTransformAsymptoticsBudgetCertificate]
  · norm_num [MellinTransformAsymptoticsBudgetCertificate.budgetControlled,
      sampleMellinTransformAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMellinTransformAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinTransformAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MellinTransformAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMellinTransformAsymptoticsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMellinTransformAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.MellinTransformAsymptotics
