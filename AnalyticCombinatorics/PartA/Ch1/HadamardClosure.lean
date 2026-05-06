import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter I: Hadamard Closure

Finite coefficientwise-product checks for Hadamard products of generating
functions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.HadamardClosure

def hadamardProduct (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  a n * b n

theorem hadamardProduct_powers :
    (List.range 6).map (hadamardProduct (fun n => 2 ^ n) (fun n => 3 ^ n)) =
      [1, 6, 36, 216, 1296, 7776] := by
  native_decide

theorem hadamardProduct_id_square :
    (List.range 6).map (hadamardProduct (fun n => n) (fun n => n)) =
      [0, 1, 4, 9, 16, 25] := by
  native_decide

def diagonalExtractionToy (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  hadamardProduct a b n

theorem diagonalExtractionToy_samples :
    diagonalExtractionToy (fun n => n + 1) (fun n => 2 ^ n) 4 = 80 := by
  native_decide

def HadamardClosureSchema
    (a b : ℕ → ℕ) (N : ℕ) : Prop :=
  (List.range (N + 1)).all (fun n => hadamardProduct a b n = a n * b n) = true

theorem hadamard_closure_schema_statement :
    HadamardClosureSchema (fun n => 2 ^ n) (fun n => 3 ^ n) 8 := by
  unfold HadamardClosureSchema hadamardProduct
  native_decide

structure HadamardCoefficientWindow where
  index : ℕ
  leftCoefficient : ℕ
  rightCoefficient : ℕ
  productBound : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HadamardCoefficientWindow.productCoefficient (w : HadamardCoefficientWindow) : ℕ :=
  w.leftCoefficient * w.rightCoefficient

def HadamardCoefficientWindow.ready (w : HadamardCoefficientWindow) : Prop :=
  w.productCoefficient ≤ w.productBound + w.slack

def HadamardCoefficientWindow.certificate (w : HadamardCoefficientWindow) : ℕ :=
  w.index + w.leftCoefficient + w.rightCoefficient + w.productBound + w.slack

theorem productBound_le_certificate (w : HadamardCoefficientWindow) :
    w.productBound ≤ w.certificate := by
  unfold HadamardCoefficientWindow.certificate
  omega

def sampleHadamardCoefficientWindow : HadamardCoefficientWindow :=
  { index := 3, leftCoefficient := 8, rightCoefficient := 27, productBound := 216, slack := 0 }

example : sampleHadamardCoefficientWindow.ready := by
  norm_num [sampleHadamardCoefficientWindow, HadamardCoefficientWindow.ready,
    HadamardCoefficientWindow.productCoefficient]

example : sampleHadamardCoefficientWindow.certificate = 254 := by
  native_decide


structure HadamardClosureBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HadamardClosureBudgetCertificate.controlled
    (c : HadamardClosureBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HadamardClosureBudgetCertificate.budgetControlled
    (c : HadamardClosureBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HadamardClosureBudgetCertificate.Ready
    (c : HadamardClosureBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HadamardClosureBudgetCertificate.size
    (c : HadamardClosureBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem hadamardClosure_budgetCertificate_le_size
    (c : HadamardClosureBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHadamardClosureBudgetCertificate :
    HadamardClosureBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleHadamardClosureBudgetCertificate.Ready := by
  constructor
  · norm_num [HadamardClosureBudgetCertificate.controlled,
      sampleHadamardClosureBudgetCertificate]
  · norm_num [HadamardClosureBudgetCertificate.budgetControlled,
      sampleHadamardClosureBudgetCertificate]

example :
    sampleHadamardClosureBudgetCertificate.certificateBudgetWindow ≤
      sampleHadamardClosureBudgetCertificate.size := by
  apply hadamardClosure_budgetCertificate_le_size
  constructor
  · norm_num [HadamardClosureBudgetCertificate.controlled,
      sampleHadamardClosureBudgetCertificate]
  · norm_num [HadamardClosureBudgetCertificate.budgetControlled,
      sampleHadamardClosureBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleHadamardClosureBudgetCertificate.Ready := by
  constructor
  · norm_num [HadamardClosureBudgetCertificate.controlled,
      sampleHadamardClosureBudgetCertificate]
  · norm_num [HadamardClosureBudgetCertificate.budgetControlled,
      sampleHadamardClosureBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHadamardClosureBudgetCertificate.certificateBudgetWindow ≤
      sampleHadamardClosureBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List HadamardClosureBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHadamardClosureBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHadamardClosureBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.HadamardClosure
