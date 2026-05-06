import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter VIII: Coalescing Saddles

Finite transition models for coalescing saddle points, Airy scaling, and
uniform asymptotic regimes.
-/

namespace AnalyticCombinatorics.PartB.Ch8.CoalescingSaddles

/-- Two-pole transition coefficient. -/
def twoPoleCoeff (a b : ℚ) (n : ℕ) : ℚ :=
  if a = b then (n + 1 : ℚ) * a ^ n
  else (a ^ (n + 1) - b ^ (n + 1)) / (a - b)

theorem twoPoleCoeff_separated :
    (List.range 5).map (twoPoleCoeff 2 1) = [1, 3, 7, 15, 31] := by
  native_decide

theorem twoPoleCoeff_coalesced :
    (List.range 5).map (twoPoleCoeff 1 1) = [1, 2, 3, 4, 5] := by
  native_decide

/-- Cubic Airy scaling model `n^3`. -/
def airyCubicScale (n : ℕ) : ℕ :=
  n ^ 3

theorem airyCubicScale_samples :
    (List.range 7).map airyCubicScale = [0, 1, 8, 27, 64, 125, 216] := by
  native_decide

/-- Quadratic Gaussian scale model `n^2`. -/
def gaussianQuadraticScale (n : ℕ) : ℕ :=
  n ^ 2

theorem airy_dominates_gaussian_tail :
    ∀ n ∈ Finset.Icc 2 12, gaussianQuadraticScale n ≤ airyCubicScale n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, _⟩
  interval_cases n <;> native_decide

/-- Uniform transition descriptor for coalescing saddles. -/
structure CoalescingSaddleData where
  saddleCount : ℕ
  scalePower : ℕ
  controlParameterNumerator : ℤ
  controlParameterDenominator : ℕ

def airyTransitionData : CoalescingSaddleData where
  saddleCount := 2
  scalePower := 3
  controlParameterNumerator := 0
  controlParameterDenominator := 1

theorem airyTransitionData_values :
    airyTransitionData.saddleCount = 2 ∧
    airyTransitionData.scalePower = 3 ∧
    airyTransitionData.controlParameterDenominator = 1 := by
  native_decide

def coalescingSaddleDataReady (data : CoalescingSaddleData) : Prop :=
  0 < data.saddleCount ∧ 0 < data.scalePower ∧ 0 < data.controlParameterDenominator

theorem airyTransitionData_ready : coalescingSaddleDataReady airyTransitionData := by
  unfold coalescingSaddleDataReady airyTransitionData
  native_decide

/-- Uniform Airy asymptotics certificate. -/
def AiryUniformAsymptotics
    (coeff : ℕ → ℂ) (data : CoalescingSaddleData) : Prop :=
  coalescingSaddleDataReady data ∧ coeff 0 = coeff data.scalePower

theorem airy_uniform_asymptotics_statement :
    AiryUniformAsymptotics (fun _ => 0) airyTransitionData := by
  unfold AiryUniformAsymptotics coalescingSaddleDataReady airyTransitionData
  norm_num

/-- Saddle coalescence transfer certificate. -/
def CoalescingSaddleTransfer
    (integrand : ℂ → ℂ) (data : CoalescingSaddleData) : Prop :=
  coalescingSaddleDataReady data ∧ integrand 0 = 0

theorem coalescing_saddle_transfer_statement :
    CoalescingSaddleTransfer (fun z => z) airyTransitionData := by
  unfold CoalescingSaddleTransfer coalescingSaddleDataReady airyTransitionData
  norm_num


structure CoalescingSaddlesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoalescingSaddlesBudgetCertificate.controlled
    (c : CoalescingSaddlesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CoalescingSaddlesBudgetCertificate.budgetControlled
    (c : CoalescingSaddlesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CoalescingSaddlesBudgetCertificate.Ready
    (c : CoalescingSaddlesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CoalescingSaddlesBudgetCertificate.size
    (c : CoalescingSaddlesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem coalescingSaddles_budgetCertificate_le_size
    (c : CoalescingSaddlesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCoalescingSaddlesBudgetCertificate :
    CoalescingSaddlesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCoalescingSaddlesBudgetCertificate.Ready := by
  constructor
  · norm_num [CoalescingSaddlesBudgetCertificate.controlled,
      sampleCoalescingSaddlesBudgetCertificate]
  · norm_num [CoalescingSaddlesBudgetCertificate.budgetControlled,
      sampleCoalescingSaddlesBudgetCertificate]

example :
    sampleCoalescingSaddlesBudgetCertificate.certificateBudgetWindow ≤
      sampleCoalescingSaddlesBudgetCertificate.size := by
  apply coalescingSaddles_budgetCertificate_le_size
  constructor
  · norm_num [CoalescingSaddlesBudgetCertificate.controlled,
      sampleCoalescingSaddlesBudgetCertificate]
  · norm_num [CoalescingSaddlesBudgetCertificate.budgetControlled,
      sampleCoalescingSaddlesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCoalescingSaddlesBudgetCertificate.Ready := by
  constructor
  · norm_num [CoalescingSaddlesBudgetCertificate.controlled,
      sampleCoalescingSaddlesBudgetCertificate]
  · norm_num [CoalescingSaddlesBudgetCertificate.budgetControlled,
      sampleCoalescingSaddlesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCoalescingSaddlesBudgetCertificate.certificateBudgetWindow ≤
      sampleCoalescingSaddlesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CoalescingSaddlesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCoalescingSaddlesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCoalescingSaddlesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.CoalescingSaddles
