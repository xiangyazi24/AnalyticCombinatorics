import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite product models for ordinary generating functions.

This file records executable finite truncations used when the analytic
identity is represented coefficientwise.
-/

namespace AnalyticCombinatorics.AppA.FiniteSeriesProducts

def prefixSum (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).map a |>.sum

def convolutionAt (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).map (fun k => a k * b (n - k)) |>.sum

def truncatedProductMass (a b : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).map (convolutionAt a b) |>.sum

def finiteSupportUpTo (a : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ n, N < n → a n = 0

theorem finiteSupportUpTo_mono {a : ℕ → ℕ} {N M : ℕ}
    (h : finiteSupportUpTo a N) (hNM : N ≤ M) :
    finiteSupportUpTo a M := by
  intro n hn
  exact h n (lt_of_le_of_lt hNM hn)

theorem prefixSum_zero (a : ℕ → ℕ) :
    prefixSum a 0 = a 0 := by
  simp [prefixSum]

theorem convolutionAt_zero (a b : ℕ → ℕ) :
    convolutionAt a b 0 = a 0 * b 0 := by
  simp [convolutionAt]

theorem truncatedProductMass_zero (a b : ℕ → ℕ) :
    truncatedProductMass a b 0 = a 0 * b 0 := by
  simp [truncatedProductMass, convolutionAt]

def sampleA : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | _ => 0

def sampleB : ℕ → ℕ
  | 0 => 3
  | 1 => 5
  | _ => 0

example : prefixSum sampleA 1 = 3 := by
  native_decide

example : convolutionAt sampleA sampleB 1 = 11 := by
  native_decide

example : truncatedProductMass sampleA sampleB 1 = 14 := by
  native_decide


structure FiniteSeriesProductsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSeriesProductsBudgetCertificate.controlled
    (c : FiniteSeriesProductsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSeriesProductsBudgetCertificate.budgetControlled
    (c : FiniteSeriesProductsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSeriesProductsBudgetCertificate.Ready
    (c : FiniteSeriesProductsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSeriesProductsBudgetCertificate.size
    (c : FiniteSeriesProductsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSeriesProducts_budgetCertificate_le_size
    (c : FiniteSeriesProductsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSeriesProductsBudgetCertificate :
    FiniteSeriesProductsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteSeriesProductsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSeriesProductsBudgetCertificate.controlled,
      sampleFiniteSeriesProductsBudgetCertificate]
  · norm_num [FiniteSeriesProductsBudgetCertificate.budgetControlled,
      sampleFiniteSeriesProductsBudgetCertificate]

example :
    sampleFiniteSeriesProductsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSeriesProductsBudgetCertificate.size := by
  apply finiteSeriesProducts_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSeriesProductsBudgetCertificate.controlled,
      sampleFiniteSeriesProductsBudgetCertificate]
  · norm_num [FiniteSeriesProductsBudgetCertificate.budgetControlled,
      sampleFiniteSeriesProductsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteSeriesProductsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSeriesProductsBudgetCertificate.controlled,
      sampleFiniteSeriesProductsBudgetCertificate]
  · norm_num [FiniteSeriesProductsBudgetCertificate.budgetControlled,
      sampleFiniteSeriesProductsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSeriesProductsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSeriesProductsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteSeriesProductsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSeriesProductsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSeriesProductsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSeriesProducts
