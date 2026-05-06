import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite constraint models.

The schema records variables, clauses, and slack for finite constraint
systems.
-/

namespace AnalyticCombinatorics.AppA.FiniteConstraintModels

structure ConstraintData where
  variableCount : ℕ
  clauses : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def variablesNonempty (d : ConstraintData) : Prop :=
  0 < d.variableCount

def clausesControlled (d : ConstraintData) : Prop :=
  d.clauses ≤ d.variableCount + d.slack

def constraintReady (d : ConstraintData) : Prop :=
  variablesNonempty d ∧ clausesControlled d

def constraintBudget (d : ConstraintData) : ℕ :=
  d.variableCount + d.clauses + d.slack

theorem constraintReady.variables {d : ConstraintData}
    (h : constraintReady d) :
    variablesNonempty d ∧ clausesControlled d ∧ d.clauses ≤ constraintBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold constraintBudget
  omega

theorem clauses_le_constraintBudget (d : ConstraintData) :
    d.clauses ≤ constraintBudget d := by
  unfold constraintBudget
  omega

def sampleConstraintData : ConstraintData :=
  { variableCount := 7, clauses := 9, slack := 4 }

example : constraintReady sampleConstraintData := by
  norm_num [constraintReady, variablesNonempty]
  norm_num [clausesControlled, sampleConstraintData]

example : constraintBudget sampleConstraintData = 20 := by
  native_decide

structure ConstraintWindow where
  variableCount : ℕ
  clauses : ℕ
  constraintSlack : ℕ
  witnessBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConstraintWindow.clausesControlled (w : ConstraintWindow) : Prop :=
  w.clauses ≤ w.variableCount + w.constraintSlack + w.slack

def ConstraintWindow.witnessControlled (w : ConstraintWindow) : Prop :=
  w.witnessBudget ≤ w.variableCount + w.clauses + w.constraintSlack + w.slack

def constraintWindowReady (w : ConstraintWindow) : Prop :=
  0 < w.variableCount ∧
    w.clausesControlled ∧
    w.witnessControlled

def ConstraintWindow.certificate (w : ConstraintWindow) : ℕ :=
  w.variableCount + w.clauses + w.constraintSlack + w.slack

theorem constraint_witnessBudget_le_certificate {w : ConstraintWindow}
    (h : constraintWindowReady w) :
    w.witnessBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hwitness⟩
  exact hwitness

def sampleConstraintWindow : ConstraintWindow :=
  { variableCount := 7, clauses := 9, constraintSlack := 4, witnessBudget := 19, slack := 0 }

example : constraintWindowReady sampleConstraintWindow := by
  norm_num [constraintWindowReady, ConstraintWindow.clausesControlled,
    ConstraintWindow.witnessControlled, sampleConstraintWindow]

example : sampleConstraintWindow.certificate = 20 := by
  native_decide


structure FiniteConstraintModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteConstraintModelsBudgetCertificate.controlled
    (c : FiniteConstraintModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteConstraintModelsBudgetCertificate.budgetControlled
    (c : FiniteConstraintModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteConstraintModelsBudgetCertificate.Ready
    (c : FiniteConstraintModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteConstraintModelsBudgetCertificate.size
    (c : FiniteConstraintModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteConstraintModels_budgetCertificate_le_size
    (c : FiniteConstraintModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteConstraintModelsBudgetCertificate :
    FiniteConstraintModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteConstraintModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteConstraintModelsBudgetCertificate.controlled,
      sampleFiniteConstraintModelsBudgetCertificate]
  · norm_num [FiniteConstraintModelsBudgetCertificate.budgetControlled,
      sampleFiniteConstraintModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteConstraintModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteConstraintModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteConstraintModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteConstraintModelsBudgetCertificate.controlled,
      sampleFiniteConstraintModelsBudgetCertificate]
  · norm_num [FiniteConstraintModelsBudgetCertificate.budgetControlled,
      sampleFiniteConstraintModelsBudgetCertificate]

example :
    sampleFiniteConstraintModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteConstraintModelsBudgetCertificate.size := by
  apply finiteConstraintModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteConstraintModelsBudgetCertificate.controlled,
      sampleFiniteConstraintModelsBudgetCertificate]
  · norm_num [FiniteConstraintModelsBudgetCertificate.budgetControlled,
      sampleFiniteConstraintModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteConstraintModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteConstraintModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteConstraintModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteConstraintModels
