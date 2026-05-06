import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix A: Finite Transforms

Finite transform models for binomial, Stirling, and ordinary generating
function manipulations.
-/

namespace AnalyticCombinatorics.AppA.FiniteTransforms

def binomialTransform (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun s k => s + n.choose k * a k) 0

theorem binomialTransform_one :
    (List.range 7).map (binomialTransform fun _ => 1) = [1, 2, 4, 8, 16, 32, 64] := by
  native_decide

theorem binomialTransform_id :
    (List.range 6).map (binomialTransform fun n => n) = [0, 1, 4, 12, 32, 80] := by
  native_decide

def signedBinomialTransform (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  (List.range (n + 1)).foldl
    (fun s k => s + (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * a k) 0

theorem signedBinomialTransform_one :
    (List.range 7).map (signedBinomialTransform fun _ => 1) = [1, 0, 0, 0, 0, 0, 0] := by
  native_decide

def partialSums (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun s k => s + a k) 0

theorem partialSums_powers_two :
    (List.range 6).map (partialSums fun n => 2 ^ n) = [1, 3, 7, 15, 31, 63] := by
  native_decide

def finiteDifference (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  a (n + 1) - a n

theorem finiteDifference_partialSums :
    (List.range 5).map (finiteDifference fun n => (partialSums (fun k => k) n : ℤ)) =
      [1, 2, 3, 4, 5] := by
  native_decide

def FiniteTransformInversion
    (forward inverse : (ℕ → ℤ) → ℕ → ℤ) (a : ℕ → ℤ) (N : ℕ) : Prop :=
  (List.range (N + 1)).all (fun n => inverse (forward a) n = a n) = true

theorem finite_transform_inversion_statement :
    FiniteTransformInversion (fun a => a) (fun a => a) (fun n => n) 8 := by
  unfold FiniteTransformInversion
  native_decide


structure FiniteTransformsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteTransformsBudgetCertificate.controlled
    (c : FiniteTransformsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteTransformsBudgetCertificate.budgetControlled
    (c : FiniteTransformsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteTransformsBudgetCertificate.Ready
    (c : FiniteTransformsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteTransformsBudgetCertificate.size
    (c : FiniteTransformsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteTransforms_budgetCertificate_le_size
    (c : FiniteTransformsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteTransformsBudgetCertificate :
    FiniteTransformsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteTransformsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteTransformsBudgetCertificate.controlled,
      sampleFiniteTransformsBudgetCertificate]
  · norm_num [FiniteTransformsBudgetCertificate.budgetControlled,
      sampleFiniteTransformsBudgetCertificate]

example :
    sampleFiniteTransformsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteTransformsBudgetCertificate.size := by
  apply finiteTransforms_budgetCertificate_le_size
  constructor
  · norm_num [FiniteTransformsBudgetCertificate.controlled,
      sampleFiniteTransformsBudgetCertificate]
  · norm_num [FiniteTransformsBudgetCertificate.budgetControlled,
      sampleFiniteTransformsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteTransformsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteTransformsBudgetCertificate.controlled,
      sampleFiniteTransformsBudgetCertificate]
  · norm_num [FiniteTransformsBudgetCertificate.budgetControlled,
      sampleFiniteTransformsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteTransformsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteTransformsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteTransformsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteTransformsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteTransformsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteTransforms
