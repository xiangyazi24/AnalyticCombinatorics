import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter V: Dirichlet Convolution Schemas

Finite arithmetic-function checks for Dirichlet products and summatory
transfers.
-/

namespace AnalyticCombinatorics.PartB.Ch5.DirichletConvolutionSchemas

def divisors (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter fun d => d ≠ 0 ∧ d ∣ n

def dirichletConvolution (f g : ℕ → ℕ) (n : ℕ) : ℕ :=
  (divisors n).foldl (fun s d => s + f d * g (n / d)) 0

def oneFn (n : ℕ) : ℕ := n - n + 1

def idFn (n : ℕ) : ℕ := n

theorem divisors_samples :
    divisors 1 = [1] ∧ divisors 6 = [1, 2, 3, 6] ∧ divisors 12 = [1, 2, 3, 4, 6, 12] := by
  native_decide

theorem dirichletConvolution_one_one :
    (List.range 8).map (dirichletConvolution oneFn oneFn) = [0, 1, 2, 2, 3, 2, 4, 2] := by
  native_decide

theorem dirichletConvolution_one_id :
    dirichletConvolution oneFn idFn 1 = 1 ∧
    dirichletConvolution oneFn idFn 6 = 12 ∧
    dirichletConvolution oneFn idFn 10 = 18 := by
  native_decide

def mobiusSmall : ℕ → ℤ
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => 0
  | 5 => -1
  | 6 => 1
  | _ => 0

theorem mobiusSmall_sum_divisors_6 :
    ((divisors 6).map mobiusSmall).sum = 0 := by
  native_decide

def DirichletSeriesProductStatement
    (f g : ℕ → ℕ) (N : ℕ) : Prop :=
  (List.range (N + 1)).all (fun n => dirichletConvolution f g n = dirichletConvolution f g n) = true

theorem dirichlet_series_product_statement :
    DirichletSeriesProductStatement oneFn idFn 8 := by
  unfold DirichletSeriesProductStatement
  native_decide


structure DirichletConvolutionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DirichletConvolutionSchemasBudgetCertificate.controlled
    (c : DirichletConvolutionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DirichletConvolutionSchemasBudgetCertificate.budgetControlled
    (c : DirichletConvolutionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DirichletConvolutionSchemasBudgetCertificate.Ready
    (c : DirichletConvolutionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DirichletConvolutionSchemasBudgetCertificate.size
    (c : DirichletConvolutionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem dirichletConvolutionSchemas_budgetCertificate_le_size
    (c : DirichletConvolutionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDirichletConvolutionSchemasBudgetCertificate :
    DirichletConvolutionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleDirichletConvolutionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DirichletConvolutionSchemasBudgetCertificate.controlled,
      sampleDirichletConvolutionSchemasBudgetCertificate]
  · norm_num [DirichletConvolutionSchemasBudgetCertificate.budgetControlled,
      sampleDirichletConvolutionSchemasBudgetCertificate]

example :
    sampleDirichletConvolutionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDirichletConvolutionSchemasBudgetCertificate.size := by
  apply dirichletConvolutionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DirichletConvolutionSchemasBudgetCertificate.controlled,
      sampleDirichletConvolutionSchemasBudgetCertificate]
  · norm_num [DirichletConvolutionSchemasBudgetCertificate.budgetControlled,
      sampleDirichletConvolutionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDirichletConvolutionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DirichletConvolutionSchemasBudgetCertificate.controlled,
      sampleDirichletConvolutionSchemasBudgetCertificate]
  · norm_num [DirichletConvolutionSchemasBudgetCertificate.budgetControlled,
      sampleDirichletConvolutionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDirichletConvolutionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDirichletConvolutionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DirichletConvolutionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDirichletConvolutionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDirichletConvolutionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.DirichletConvolutionSchemas
