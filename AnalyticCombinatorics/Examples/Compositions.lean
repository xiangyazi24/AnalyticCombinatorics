import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Integer composition examples.

Compositions of `n` into positive parts have count `1` at `n = 0` and
`2^(n-1)` for positive `n`.
-/

namespace AnalyticCombinatorics.Examples.Compositions

def compositionCount : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ n

@[simp]
theorem compositionCount_zero : compositionCount 0 = 1 := rfl

@[simp]
theorem compositionCount_succ (n : ℕ) :
    compositionCount (n + 1) = 2 ^ n := rfl

example : compositionCount 0 = 1 := by native_decide
example : compositionCount 1 = 1 := by native_decide
example : compositionCount 2 = 2 := by native_decide
example : compositionCount 3 = 4 := by native_decide
example : compositionCount 4 = 8 := by native_decide
example : compositionCount 5 = 16 := by native_decide
example : compositionCount 10 = 512 := by native_decide

theorem compositionCount_values_0_to_10 :
    (List.range 11).map compositionCount =
      [1, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512] := by
  native_decide

def positiveCompositionWord (n : ℕ) :=
  { xs : List ℕ // xs.sum = n ∧ ∀ x ∈ xs, 0 < x }

def weakCompositionWord (n k : ℕ) :=
  { xs : List ℕ // xs.length = k ∧ xs.sum = n }

def weakCompositionCount (n k : ℕ) : ℕ :=
  Nat.choose (n + k - 1) (k - 1)

structure CompositionWindow where
  total : ℕ
  parts : ℕ
  maxPart : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompositionWindow.positiveReady (w : CompositionWindow) : Prop :=
  0 < w.parts ∧ w.parts ≤ w.total + w.slack

def CompositionWindow.boundedReady (w : CompositionWindow) : Prop :=
  w.total ≤ w.parts * w.maxPart + w.slack

def CompositionWindow.certificate (w : CompositionWindow) : ℕ :=
  w.total + w.parts + w.maxPart + w.slack

theorem parts_le_certificate (w : CompositionWindow) :
    w.parts ≤ w.certificate := by
  unfold CompositionWindow.certificate
  omega

theorem maxPart_le_certificate (w : CompositionWindow) :
    w.maxPart ≤ w.certificate := by
  unfold CompositionWindow.certificate
  omega

def sampleCompositionWindow : CompositionWindow :=
  { total := 7, parts := 3, maxPart := 4, slack := 0 }

example : sampleCompositionWindow.positiveReady := by
  norm_num [sampleCompositionWindow, CompositionWindow.positiveReady]

example : sampleCompositionWindow.boundedReady := by
  norm_num [sampleCompositionWindow, CompositionWindow.boundedReady]

example : weakCompositionCount 5 3 = 21 := by
  native_decide

structure CompositionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompositionsBudgetCertificate.controlled
    (c : CompositionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CompositionsBudgetCertificate.budgetControlled
    (c : CompositionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CompositionsBudgetCertificate.Ready
    (c : CompositionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CompositionsBudgetCertificate.size (c : CompositionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem compositions_budgetCertificate_le_size
    (c : CompositionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleCompositionsBudgetCertificate : CompositionsBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleCompositionsBudgetCertificate.Ready := by
  constructor
  · norm_num [CompositionsBudgetCertificate.controlled,
      sampleCompositionsBudgetCertificate]
  · norm_num [CompositionsBudgetCertificate.budgetControlled,
      sampleCompositionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCompositionsBudgetCertificate.Ready := by
  constructor
  · norm_num [CompositionsBudgetCertificate.controlled,
      sampleCompositionsBudgetCertificate]
  · norm_num [CompositionsBudgetCertificate.budgetControlled,
      sampleCompositionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCompositionsBudgetCertificate.certificateBudgetWindow ≤
      sampleCompositionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CompositionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCompositionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCompositionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.Compositions
