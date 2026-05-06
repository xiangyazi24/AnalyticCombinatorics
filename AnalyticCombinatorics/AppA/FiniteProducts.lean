import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite products used by coefficient constructions.

This module provides small executable product models without depending on
any project-local generating-function files.
-/

namespace AnalyticCombinatorics.AppA.FiniteProducts

def productUpTo (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).map a |>.prod

def boundedFactor (a : ℕ → ℕ) (N bound : ℕ) : Prop :=
  ∀ n, n ≤ N → a n ≤ bound

def allFactorsOne (n : ℕ) : ℕ := n - n + 1

theorem productUpTo_zero (a : ℕ → ℕ) :
    productUpTo a 0 = a 0 := by
  simp [productUpTo]

theorem productUpTo_one_factors (N : ℕ) :
    productUpTo allFactorsOne N = 1 := by
  unfold productUpTo
  generalize List.range (N + 1) = xs
  induction xs with
  | nil => simp
  | cons x xs ih => simp [allFactorsOne, ih]

theorem boundedFactor_mono {a : ℕ → ℕ} {N b c : ℕ}
    (h : boundedFactor a N b) (hbc : b ≤ c) :
    boundedFactor a N c := by
  intro n hn
  exact le_trans (h n hn) hbc

def sampleFactors : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | _ => 1

example : productUpTo sampleFactors 2 = 30 := by
  native_decide

example : boundedFactor sampleFactors 2 5 := by
  intro n hn
  interval_cases n <;> native_decide

structure ProductWindow where
  factorCount : ℕ
  factorBound : ℕ
  productBudget : ℕ
  evaluationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProductWindow.productControlled (w : ProductWindow) : Prop :=
  w.productBudget ≤ (w.factorBound + 1) * (w.factorCount + 1) + w.slack

def ProductWindow.evaluationControlled (w : ProductWindow) : Prop :=
  w.evaluationBudget ≤ w.productBudget + w.factorCount + w.slack

def productWindowReady (w : ProductWindow) : Prop :=
  0 < w.factorBound ∧
    w.productControlled ∧
    w.evaluationControlled

def ProductWindow.certificate (w : ProductWindow) : ℕ :=
  w.productBudget + w.factorCount + w.slack

theorem productWindow_evaluationBudget_le_certificate {w : ProductWindow}
    (h : productWindowReady w) :
    w.evaluationBudget ≤ w.certificate := by
  rcases h with ⟨_, _, heval⟩
  exact heval

def sampleProductWindow : ProductWindow :=
  { factorCount := 2, factorBound := 5, productBudget := 18, evaluationBudget := 20, slack := 0 }

example : productWindowReady sampleProductWindow := by
  norm_num [productWindowReady, ProductWindow.productControlled,
    ProductWindow.evaluationControlled, sampleProductWindow]

example : sampleProductWindow.certificate = 20 := by
  native_decide


structure FiniteProductsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteProductsBudgetCertificate.controlled
    (c : FiniteProductsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteProductsBudgetCertificate.budgetControlled
    (c : FiniteProductsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteProductsBudgetCertificate.Ready
    (c : FiniteProductsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteProductsBudgetCertificate.size
    (c : FiniteProductsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteProducts_budgetCertificate_le_size
    (c : FiniteProductsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteProductsBudgetCertificate :
    FiniteProductsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteProductsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteProductsBudgetCertificate.controlled,
      sampleFiniteProductsBudgetCertificate]
  · norm_num [FiniteProductsBudgetCertificate.budgetControlled,
      sampleFiniteProductsBudgetCertificate]

example :
    sampleFiniteProductsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteProductsBudgetCertificate.size := by
  apply finiteProducts_budgetCertificate_le_size
  constructor
  · norm_num [FiniteProductsBudgetCertificate.controlled,
      sampleFiniteProductsBudgetCertificate]
  · norm_num [FiniteProductsBudgetCertificate.budgetControlled,
      sampleFiniteProductsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteProductsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteProductsBudgetCertificate.controlled,
      sampleFiniteProductsBudgetCertificate]
  · norm_num [FiniteProductsBudgetCertificate.budgetControlled,
      sampleFiniteProductsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteProductsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteProductsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteProductsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteProductsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteProductsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteProducts
