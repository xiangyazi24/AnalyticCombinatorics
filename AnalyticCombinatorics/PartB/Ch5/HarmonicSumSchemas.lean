import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite harmonic-sum schemas.

The file avoids real-valued harmonic numbers and records numerator and
denominator bookkeeping for finite summatory estimates.
-/

namespace AnalyticCombinatorics.PartB.Ch5.HarmonicSumSchemas

def reciprocalDenominatorProduct (N : ℕ) : ℕ :=
  (List.range N).map (fun k => k + 1) |>.prod

def harmonicIndexPositive (N : ℕ) : Prop :=
  0 < N

def harmonicWindow (start width : ℕ) : List ℕ :=
  (List.range width).map (fun k => start + k + 1)

theorem reciprocalDenominatorProduct_zero :
    reciprocalDenominatorProduct 0 = 1 := by
  rfl

theorem harmonicWindow_length (start width : ℕ) :
    (harmonicWindow start width).length = width := by
  simp [harmonicWindow]

theorem harmonicIndexPositive_succ (N : ℕ) :
    harmonicIndexPositive (N + 1) := by
  unfold harmonicIndexPositive
  omega

example : reciprocalDenominatorProduct 4 = 24 := by
  native_decide

example : harmonicWindow 3 4 = [4, 5, 6, 7] := by
  native_decide

structure HarmonicSumWindow where
  cutoff : ℕ
  denominatorProduct : ℕ
  numeratorBound : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HarmonicSumWindow.denominatorReady (w : HarmonicSumWindow) : Prop :=
  0 < w.denominatorProduct

def HarmonicSumWindow.numeratorControlled (w : HarmonicSumWindow) : Prop :=
  w.numeratorBound ≤ w.cutoff * w.denominatorProduct + w.slack

def HarmonicSumWindow.certificate (w : HarmonicSumWindow) : ℕ :=
  w.cutoff + w.denominatorProduct + w.numeratorBound + w.slack

theorem numeratorBound_le_certificate (w : HarmonicSumWindow) :
    w.numeratorBound ≤ w.certificate := by
  unfold HarmonicSumWindow.certificate
  omega

def sampleHarmonicSumWindow : HarmonicSumWindow :=
  { cutoff := 4, denominatorProduct := 24, numeratorBound := 50, slack := 0 }

example : sampleHarmonicSumWindow.denominatorReady := by
  norm_num [sampleHarmonicSumWindow, HarmonicSumWindow.denominatorReady]

example : sampleHarmonicSumWindow.numeratorControlled := by
  norm_num [sampleHarmonicSumWindow, HarmonicSumWindow.numeratorControlled]


structure HarmonicSumSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HarmonicSumSchemasBudgetCertificate.controlled
    (c : HarmonicSumSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HarmonicSumSchemasBudgetCertificate.budgetControlled
    (c : HarmonicSumSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HarmonicSumSchemasBudgetCertificate.Ready
    (c : HarmonicSumSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HarmonicSumSchemasBudgetCertificate.size
    (c : HarmonicSumSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem harmonicSumSchemas_budgetCertificate_le_size
    (c : HarmonicSumSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHarmonicSumSchemasBudgetCertificate :
    HarmonicSumSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleHarmonicSumSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [HarmonicSumSchemasBudgetCertificate.controlled,
      sampleHarmonicSumSchemasBudgetCertificate]
  · norm_num [HarmonicSumSchemasBudgetCertificate.budgetControlled,
      sampleHarmonicSumSchemasBudgetCertificate]

example :
    sampleHarmonicSumSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleHarmonicSumSchemasBudgetCertificate.size := by
  apply harmonicSumSchemas_budgetCertificate_le_size
  constructor
  · norm_num [HarmonicSumSchemasBudgetCertificate.controlled,
      sampleHarmonicSumSchemasBudgetCertificate]
  · norm_num [HarmonicSumSchemasBudgetCertificate.budgetControlled,
      sampleHarmonicSumSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleHarmonicSumSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [HarmonicSumSchemasBudgetCertificate.controlled,
      sampleHarmonicSumSchemasBudgetCertificate]
  · norm_num [HarmonicSumSchemasBudgetCertificate.budgetControlled,
      sampleHarmonicSumSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHarmonicSumSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleHarmonicSumSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List HarmonicSumSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHarmonicSumSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHarmonicSumSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.HarmonicSumSchemas
