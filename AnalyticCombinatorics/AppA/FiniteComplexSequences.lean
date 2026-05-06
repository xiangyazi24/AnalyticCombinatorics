import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix A: Finite Complex Sequences

Finite complex-valued sequence descriptors and rational real-imaginary
models.
-/

namespace AnalyticCombinatorics.AppA.FiniteComplexSequences

structure RationalComplex where
  re : ℚ
  im : ℚ
  deriving DecidableEq

def rcAdd (z w : RationalComplex) : RationalComplex where
  re := z.re + w.re
  im := z.im + w.im

def rcMul (z w : RationalComplex) : RationalComplex where
  re := z.re * w.re - z.im * w.im
  im := z.re * w.im + z.im * w.re

def I : RationalComplex where
  re := 0
  im := 1

def one : RationalComplex where
  re := 1
  im := 0

theorem rcMul_I_square :
    rcMul I I = { re := -1, im := 0 } := by
  native_decide

theorem rcAdd_samples :
    rcAdd { re := 1, im := 2 } { re := 3, im := -5 } = { re := 4, im := -3 } := by
  native_decide

def rcNormSq (z : RationalComplex) : ℚ :=
  z.re ^ 2 + z.im ^ 2

theorem rcNormSq_samples :
    rcNormSq one = 1 ∧ rcNormSq I = 1 ∧ rcNormSq { re := 3, im := 4 } = 25 := by
  native_decide

def ComplexSequenceBound
    (a : ℕ → RationalComplex) (bound : ℕ → ℚ) (N : ℕ) : Prop :=
  (List.range (N + 1)).all (fun n => rcNormSq (a n) ≤ bound n) = true

theorem complex_sequence_bound_statement :
    ComplexSequenceBound (fun _ => one) (fun _ => 1) 8 := by
  unfold ComplexSequenceBound rcNormSq one
  native_decide


structure FiniteComplexSequencesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteComplexSequencesBudgetCertificate.controlled
    (c : FiniteComplexSequencesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteComplexSequencesBudgetCertificate.budgetControlled
    (c : FiniteComplexSequencesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteComplexSequencesBudgetCertificate.Ready
    (c : FiniteComplexSequencesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteComplexSequencesBudgetCertificate.size
    (c : FiniteComplexSequencesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteComplexSequences_budgetCertificate_le_size
    (c : FiniteComplexSequencesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteComplexSequencesBudgetCertificate :
    FiniteComplexSequencesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteComplexSequencesBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteComplexSequencesBudgetCertificate.controlled,
      sampleFiniteComplexSequencesBudgetCertificate]
  · norm_num [FiniteComplexSequencesBudgetCertificate.budgetControlled,
      sampleFiniteComplexSequencesBudgetCertificate]

example :
    sampleFiniteComplexSequencesBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteComplexSequencesBudgetCertificate.size := by
  apply finiteComplexSequences_budgetCertificate_le_size
  constructor
  · norm_num [FiniteComplexSequencesBudgetCertificate.controlled,
      sampleFiniteComplexSequencesBudgetCertificate]
  · norm_num [FiniteComplexSequencesBudgetCertificate.budgetControlled,
      sampleFiniteComplexSequencesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteComplexSequencesBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteComplexSequencesBudgetCertificate.controlled,
      sampleFiniteComplexSequencesBudgetCertificate]
  · norm_num [FiniteComplexSequencesBudgetCertificate.budgetControlled,
      sampleFiniteComplexSequencesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteComplexSequencesBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteComplexSequencesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteComplexSequencesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteComplexSequencesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteComplexSequencesBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteComplexSequences
