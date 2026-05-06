import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Padovan-style compositions.

Compositions with parts in `{2, 3}` satisfy `a n = a (n - 2) + a (n - 3)`.
-/

namespace AnalyticCombinatorics.Examples.Padovan

structure PadovanCompositionWindow where
  totalSize : ℕ
  partCount : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def padovanWindowReady (w : PadovanCompositionWindow) : Prop :=
  0 < w.totalSize ∧ w.partCount ≤ w.totalSize + w.slack

def padovanWindowBudget (w : PadovanCompositionWindow) : ℕ :=
  w.totalSize + w.partCount + w.slack

theorem padovanWindowReady.certificate {w : PadovanCompositionWindow}
    (h : padovanWindowReady w) :
    0 < w.totalSize ∧ w.partCount ≤ w.totalSize + w.slack ∧
      w.partCount ≤ padovanWindowBudget w := by
  rcases h with ⟨hsize, hparts⟩
  refine ⟨hsize, hparts, ?_⟩
  unfold padovanWindowBudget
  omega

/-- Count of compositions of `n` into parts `2` and `3`. -/
def padovanCompositionCount : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | n + 3 => padovanCompositionCount (n + 1) + padovanCompositionCount n

theorem padovanCompositionCount_rec (n : ℕ) :
    padovanCompositionCount (n + 3) =
      padovanCompositionCount (n + 1) + padovanCompositionCount n := rfl

def samplePadovanWindow : PadovanCompositionWindow :=
  { totalSize := 10, partCount := 4, slack := 0 }

example : padovanWindowReady samplePadovanWindow := by
  norm_num [padovanWindowReady, samplePadovanWindow]
example : padovanCompositionCount 0 = 1 := by native_decide
example : padovanCompositionCount 1 = 0 := by native_decide
example : padovanCompositionCount 2 = 1 := by native_decide
example : padovanCompositionCount 3 = 1 := by native_decide
example : padovanCompositionCount 4 = 1 := by native_decide
example : padovanCompositionCount 5 = 2 := by native_decide
example : padovanCompositionCount 6 = 2 := by native_decide
example : padovanCompositionCount 7 = 3 := by native_decide
example : padovanCompositionCount 8 = 4 := by native_decide
example : padovanCompositionCount 9 = 5 := by native_decide
example : padovanCompositionCount 10 = 7 := by native_decide
example : padovanWindowBudget samplePadovanWindow = 14 := by native_decide
example :
    (List.range 8).map padovanCompositionCount = [1, 0, 1, 1, 1, 2, 2, 3] := by
  native_decide

structure PadovanBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PadovanBudgetCertificate.controlled
    (c : PadovanBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PadovanBudgetCertificate.budgetControlled
    (c : PadovanBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PadovanBudgetCertificate.Ready (c : PadovanBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PadovanBudgetCertificate.size (c : PadovanBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem padovan_budgetCertificate_le_size
    (c : PadovanBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def samplePadovanBudgetCertificate : PadovanBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : samplePadovanBudgetCertificate.Ready := by
  constructor
  · norm_num [PadovanBudgetCertificate.controlled,
      samplePadovanBudgetCertificate]
  · norm_num [PadovanBudgetCertificate.budgetControlled,
      samplePadovanBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePadovanBudgetCertificate.Ready := by
  constructor
  · norm_num [PadovanBudgetCertificate.controlled,
      samplePadovanBudgetCertificate]
  · norm_num [PadovanBudgetCertificate.budgetControlled,
      samplePadovanBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePadovanBudgetCertificate.certificateBudgetWindow ≤
      samplePadovanBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PadovanBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePadovanBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePadovanBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.Padovan
