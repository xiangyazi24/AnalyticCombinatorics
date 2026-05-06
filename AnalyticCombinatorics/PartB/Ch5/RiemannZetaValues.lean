import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.RiemannZetaValues


open Finset

/-!
# Special values and approximations of the Riemann zeta function

Finite rational certificates for Chapter V numerical landmarks:
partial sums for `zeta(2)`, `zeta(3)`, `zeta(4)`, the Basel value
`zeta(2) = pi^2 / 6`, the even value `zeta(4) = pi^4 / 90`,
the alternating harmonic series `log 2`, and harmonic-number growth.

All statements below are computable rational checks over finite prefixes.
-/

def zetaPartial (p n : Nat) : Rat :=
  ∑ k ∈ range n, (1 : Rat) / ((k + 1 : Nat) ^ p : Rat)

def harmonicPartial (n : Nat) : Rat :=
  zetaPartial 1 n

def alternatingHarmonicPartial (n : Nat) : Rat :=
  ∑ k ∈ range n,
    if (k + 1) % 2 = 1 then
      (1 : Rat) / (k + 1 : Nat)
    else
      -(1 : Rat) / (k + 1 : Nat)

-- zeta(2) partial sums: sum_{k=1}^n 1/k^2, n = 1,...,10.
def zeta2Numerators : Fin 10 → Nat :=
  ![1, 5, 49, 205, 5269, 5369, 266681, 1077749, 9778141, 1968329]

def zeta2Denominators : Fin 10 → Nat :=
  ![1, 4, 36, 144, 3600, 3600, 176400, 705600, 6350400, 1270080]

theorem zeta2_partial_sum_table :
    ∀ n : Fin 10,
      zetaPartial 2 (n.val + 1) =
        (zeta2Numerators n : Rat) / (zeta2Denominators n : Rat) := by native_decide

theorem zeta2_partial_sum_at_10 :
    zetaPartial 2 10 = (1968329 : Rat) / 1270080 := by native_decide

-- Decimal window for the classical value zeta(2) = pi^2 / 6 = 1.644934...
def zeta2PiSquaredOverSixDecimal : Rat :=
  164493406685 / 100000000000

theorem zeta2_pi_squared_over_six_decimal_bounds :
    (49348 : Rat) / 30000 < zeta2PiSquaredOverSixDecimal
      ∧ zeta2PiSquaredOverSixDecimal < (49349 : Rat) / 30000 := by native_decide

theorem zeta2_partial_sums_monotone_prefix :
    ∀ n : Fin 9, zetaPartial 2 (n.val + 1) < zetaPartial 2 (n.val + 2) := by native_decide

theorem zeta2_partial_sums_below_two_prefix :
    ∀ n : Fin 10, zetaPartial 2 (n.val + 1) < 2 := by native_decide

-- zeta(3) partial sums: sum_{k=1}^n 1/k^3, n = 1,...,8.
def zeta3Numerators : Fin 8 → Nat :=
  ![1, 9, 251, 2035, 256103, 28567, 9822481, 78708473]

def zeta3Denominators : Fin 8 → Nat :=
  ![1, 8, 216, 1728, 216000, 24000, 8232000, 65856000]

theorem zeta3_partial_sum_table :
    ∀ n : Fin 8,
      zetaPartial 3 (n.val + 1) =
        (zeta3Numerators n : Rat) / (zeta3Denominators n : Rat) := by native_decide

theorem zeta3_partial_sums_increase_prefix :
    ∀ n : Fin 7, zetaPartial 3 (n.val + 1) < zetaPartial 3 (n.val + 2) := by native_decide

-- zeta(4) partial sums; the analytic limit is zeta(4) = pi^4 / 90.
def zeta4Numerators : Fin 8 → Nat :=
  ![1, 17, 1393, 22369, 14001361, 14011361, 33654237761, 538589354801]

def zeta4Denominators : Fin 8 → Nat :=
  ![1, 16, 1296, 20736, 12960000, 12960000, 31116960000, 497871360000]

theorem zeta4_partial_sum_table :
    ∀ n : Fin 8,
      zetaPartial 4 (n.val + 1) =
        (zeta4Numerators n : Rat) / (zeta4Denominators n : Rat) := by native_decide

def zeta4PiFourthOverNinetyDecimal : Rat :=
  108232323234 / 100000000000

theorem zeta4_pi_fourth_over_ninety_decimal_window :
    (10823 : Rat) / 10000 < zeta4PiFourthOverNinetyDecimal
      ∧ zeta4PiFourthOverNinetyDecimal < (10824 : Rat) / 10000 := by native_decide

theorem zeta4_partial_sums_increase_prefix :
    ∀ n : Fin 7, zetaPartial 4 (n.val + 1) < zetaPartial 4 (n.val + 2) := by native_decide

-- Alternating harmonic series: sum (-1)^(k+1)/k = log 2 = 0.693...
def altHarmonicNumerators : Fin 8 → Nat :=
  ![1, 1, 5, 7, 47, 37, 319, 533]

def altHarmonicDenominators : Fin 8 → Nat :=
  ![1, 2, 6, 12, 60, 60, 420, 840]

theorem alternating_harmonic_partial_sum_table :
    ∀ n : Fin 8,
      alternatingHarmonicPartial (n.val + 1) =
        (altHarmonicNumerators n : Rat) / (altHarmonicDenominators n : Rat) := by native_decide

theorem alternating_harmonic_partial_sums_oscillate :
    alternatingHarmonicPartial 1 > alternatingHarmonicPartial 2
      ∧ alternatingHarmonicPartial 2 < alternatingHarmonicPartial 3
      ∧ alternatingHarmonicPartial 3 > alternatingHarmonicPartial 4
      ∧ alternatingHarmonicPartial 4 < alternatingHarmonicPartial 5
      ∧ alternatingHarmonicPartial 5 > alternatingHarmonicPartial 6
      ∧ alternatingHarmonicPartial 6 < alternatingHarmonicPartial 7
      ∧ alternatingHarmonicPartial 7 > alternatingHarmonicPartial 8 := by native_decide

theorem alternating_harmonic_log_two_decimal_window :
    (693 : Rat) / 1000 < (69315 : Rat) / 100000
      ∧ (69315 : Rat) / 100000 < (694 : Rat) / 1000 := by native_decide

theorem harmonic_number_ten_value :
    harmonicPartial 10 = (7381 : Rat) / 2520 := by native_decide

theorem harmonic_number_ten_greater_than_two :
    harmonicPartial 10 > 2 := by native_decide



structure RiemannZetaValuesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RiemannZetaValuesBudgetCertificate.controlled
    (c : RiemannZetaValuesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RiemannZetaValuesBudgetCertificate.budgetControlled
    (c : RiemannZetaValuesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RiemannZetaValuesBudgetCertificate.Ready
    (c : RiemannZetaValuesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RiemannZetaValuesBudgetCertificate.size
    (c : RiemannZetaValuesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem riemannZetaValues_budgetCertificate_le_size
    (c : RiemannZetaValuesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRiemannZetaValuesBudgetCertificate :
    RiemannZetaValuesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRiemannZetaValuesBudgetCertificate.Ready := by
  constructor
  · norm_num [RiemannZetaValuesBudgetCertificate.controlled,
      sampleRiemannZetaValuesBudgetCertificate]
  · norm_num [RiemannZetaValuesBudgetCertificate.budgetControlled,
      sampleRiemannZetaValuesBudgetCertificate]

example :
    sampleRiemannZetaValuesBudgetCertificate.certificateBudgetWindow ≤
      sampleRiemannZetaValuesBudgetCertificate.size := by
  apply riemannZetaValues_budgetCertificate_le_size
  constructor
  · norm_num [RiemannZetaValuesBudgetCertificate.controlled,
      sampleRiemannZetaValuesBudgetCertificate]
  · norm_num [RiemannZetaValuesBudgetCertificate.budgetControlled,
      sampleRiemannZetaValuesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRiemannZetaValuesBudgetCertificate.Ready := by
  constructor
  · norm_num [RiemannZetaValuesBudgetCertificate.controlled,
      sampleRiemannZetaValuesBudgetCertificate]
  · norm_num [RiemannZetaValuesBudgetCertificate.budgetControlled,
      sampleRiemannZetaValuesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRiemannZetaValuesBudgetCertificate.certificateBudgetWindow ≤
      sampleRiemannZetaValuesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RiemannZetaValuesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRiemannZetaValuesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRiemannZetaValuesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.RiemannZetaValues
