import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Inverse functions.

Finite inversion-window bookkeeping for singular expansions obtained from
functional inverses.
-/

namespace AnalyticCombinatorics.PartB.Ch6.InverseFunctions

/-- Finite composition check for inverse functions on sampled naturals. -/
def inversePairCheck (f g : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => f (g n) = n ∧ g (f n) = n

/-- Shift map used as a sample local inverse on positive samples. -/
def shiftUp (n : ℕ) : ℕ :=
  n + 1

def shiftDown : ℕ → ℕ
  | 0 => 0
  | n + 1 => n

/-- Finite inverse check after excluding the non-invertible boundary point. -/
def inversePairCheckAfter (f g : ℕ → ℕ) (start N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n < start then true else f (g n) = n

theorem shift_inverse_window :
    inversePairCheckAfter shiftUp shiftDown 1 24 = true := by
  unfold inversePairCheckAfter shiftUp shiftDown
  native_decide

theorem identity_inverse_window :
    inversePairCheck (fun n => n) (fun n => n) 24 = true := by
  unfold inversePairCheck
  native_decide

structure InverseFunctionWindow where
  equationDepth : ℕ
  inverseDepth : ℕ
  expansionDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def inverseFunctionReady (w : InverseFunctionWindow) : Prop :=
  0 < w.equationDepth ∧
    w.inverseDepth ≤ w.equationDepth + w.expansionDepth + w.slack

def inverseFunctionBudget (w : InverseFunctionWindow) : ℕ :=
  w.equationDepth + w.inverseDepth + w.expansionDepth + w.slack

theorem inverseDepth_le_inverseFunctionBudget (w : InverseFunctionWindow) :
    w.inverseDepth ≤ inverseFunctionBudget w := by
  unfold inverseFunctionBudget
  omega

def sampleInverseFunctionWindow : InverseFunctionWindow :=
  { equationDepth := 5, inverseDepth := 7, expansionDepth := 3, slack := 1 }

example : inverseFunctionReady sampleInverseFunctionWindow := by
  norm_num [inverseFunctionReady, sampleInverseFunctionWindow]

structure InverseFunctionsBudgetCertificate where
  equationWindow : ℕ
  inverseWindow : ℕ
  expansionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def InverseFunctionsBudgetCertificate.controlled
    (c : InverseFunctionsBudgetCertificate) : Prop :=
  0 < c.equationWindow ∧
    c.inverseWindow ≤ c.equationWindow + c.expansionWindow + c.slack

def InverseFunctionsBudgetCertificate.budgetControlled
    (c : InverseFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.equationWindow + c.inverseWindow + c.expansionWindow + c.slack

def InverseFunctionsBudgetCertificate.Ready
    (c : InverseFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def InverseFunctionsBudgetCertificate.size
    (c : InverseFunctionsBudgetCertificate) : ℕ :=
  c.equationWindow + c.inverseWindow + c.expansionWindow + c.slack

theorem inverseFunctions_budgetCertificate_le_size
    (c : InverseFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleInverseFunctionsBudgetCertificate : InverseFunctionsBudgetCertificate :=
  { equationWindow := 5
    inverseWindow := 7
    expansionWindow := 3
    certificateBudgetWindow := 16
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleInverseFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [InverseFunctionsBudgetCertificate.controlled,
      sampleInverseFunctionsBudgetCertificate]
  · norm_num [InverseFunctionsBudgetCertificate.budgetControlled,
      sampleInverseFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleInverseFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleInverseFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleInverseFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [InverseFunctionsBudgetCertificate.controlled,
      sampleInverseFunctionsBudgetCertificate]
  · norm_num [InverseFunctionsBudgetCertificate.budgetControlled,
      sampleInverseFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List InverseFunctionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleInverseFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleInverseFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.InverseFunctions
