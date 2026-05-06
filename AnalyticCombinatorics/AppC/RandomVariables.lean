import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix C: random variables.

Finite support, moment, and range-window bookkeeping.
-/

namespace AnalyticCombinatorics.AppC.RandomVariables

/-- Push-forward mass of a finite random variable, sampled by exact fibers. -/
def fiberCount (X : ℕ → ℕ) (value N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total k => if X k = value then total + 1 else total) 0

/-- Finite boundedness check for a random variable on a finite support. -/
def boundedRandomVariableCheck (X : ℕ → ℕ) (bound N : ℕ) : Bool :=
  (List.range (N + 1)).all fun k => X k ≤ bound

/-- First raw moment numerator under the counting measure. -/
def firstMomentNumerator (X : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total k => total + X k) 0

def parityVariable (n : ℕ) : ℕ :=
  n % 2

theorem parityVariable_bounded :
    boundedRandomVariableCheck parityVariable 1 16 = true := by
  unfold boundedRandomVariableCheck parityVariable
  native_decide

theorem parityVariable_fiber_samples :
    fiberCount parityVariable 0 3 = 2 ∧
    fiberCount parityVariable 1 3 = 2 ∧
    firstMomentNumerator parityVariable 3 = 2 := by
  unfold fiberCount firstMomentNumerator parityVariable
  native_decide

structure RandomVariableWindow where
  supportSize : ℕ
  rangeWindow : ℕ
  momentWindow : ℕ
  momentSlack : ℕ
deriving DecidableEq, Repr

def randomVariableWindowReady (w : RandomVariableWindow) : Prop :=
  0 < w.supportSize ∧
    w.momentWindow ≤ w.supportSize * (w.rangeWindow + 1) + w.momentSlack

def randomVariableWindowBudget (w : RandomVariableWindow) : ℕ :=
  w.supportSize + w.rangeWindow + w.momentWindow + w.momentSlack

theorem momentWindow_le_budget (w : RandomVariableWindow) :
    w.momentWindow ≤ randomVariableWindowBudget w := by
  unfold randomVariableWindowBudget
  omega

def sampleRandomVariableWindow : RandomVariableWindow :=
  { supportSize := 4, rangeWindow := 3, momentWindow := 12, momentSlack := 0 }

example : randomVariableWindowReady sampleRandomVariableWindow := by
  norm_num [randomVariableWindowReady, sampleRandomVariableWindow]

structure RandomVariablesBudgetCertificate where
  supportWindow : ℕ
  rangeWindow : ℕ
  momentWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomVariablesBudgetCertificate.controlled
    (c : RandomVariablesBudgetCertificate) : Prop :=
  0 < c.supportWindow ∧
    c.momentWindow ≤ c.supportWindow * (c.rangeWindow + 1) + c.slack

def RandomVariablesBudgetCertificate.budgetControlled
    (c : RandomVariablesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.supportWindow + c.rangeWindow + c.momentWindow + c.slack

def RandomVariablesBudgetCertificate.Ready
    (c : RandomVariablesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomVariablesBudgetCertificate.size
    (c : RandomVariablesBudgetCertificate) : ℕ :=
  c.supportWindow + c.rangeWindow + c.momentWindow + c.slack

theorem randomVariables_budgetCertificate_le_size
    (c : RandomVariablesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleRandomVariablesBudgetCertificate :
    RandomVariablesBudgetCertificate :=
  { supportWindow := 4
    rangeWindow := 3
    momentWindow := 12
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomVariablesBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomVariablesBudgetCertificate.controlled,
      sampleRandomVariablesBudgetCertificate]
  · norm_num [RandomVariablesBudgetCertificate.budgetControlled,
      sampleRandomVariablesBudgetCertificate]

example : sampleRandomVariablesBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomVariablesBudgetCertificate.controlled,
      sampleRandomVariablesBudgetCertificate]
  · norm_num [RandomVariablesBudgetCertificate.budgetControlled,
      sampleRandomVariablesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleRandomVariablesBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomVariablesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RandomVariablesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleRandomVariablesBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleRandomVariablesBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.RandomVariables
