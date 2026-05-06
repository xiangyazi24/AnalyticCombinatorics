import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random-walk limit schema bookkeeping.

The data records step variance, drift budget, and lattice span for random
walk asymptotics.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomWalkLimitSchemas

structure RandomWalkData where
  stepVariance : ℕ
  driftBudget : ℕ
  latticeSpan : ℕ
deriving DecidableEq, Repr

def nonzeroStepVariance (d : RandomWalkData) : Prop :=
  0 < d.stepVariance

def unitSpan (d : RandomWalkData) : Prop :=
  d.latticeSpan = 1

def randomWalkLimitReady (d : RandomWalkData) : Prop :=
  nonzeroStepVariance d ∧ unitSpan d

def spreadBudget (d : RandomWalkData) : ℕ :=
  d.stepVariance + d.driftBudget

theorem randomWalkLimitReady.variance {d : RandomWalkData}
    (h : randomWalkLimitReady d) :
    nonzeroStepVariance d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem stepVariance_le_spreadBudget (d : RandomWalkData) :
    d.stepVariance ≤ spreadBudget d := by
  unfold spreadBudget
  omega

def sampleWalk : RandomWalkData :=
  { stepVariance := 4, driftBudget := 3, latticeSpan := 1 }

example : randomWalkLimitReady sampleWalk := by
  norm_num [randomWalkLimitReady, nonzeroStepVariance, unitSpan, sampleWalk]

example : spreadBudget sampleWalk = 7 := by
  native_decide

/-- Finite executable readiness audit for random-walk limit data. -/
def randomWalkDataListReady (data : List RandomWalkData) : Bool :=
  data.all fun d =>
    0 < d.stepVariance && d.latticeSpan = 1 && d.driftBudget ≤ d.stepVariance

theorem randomWalkDataList_readyWindow :
    randomWalkDataListReady
      [{ stepVariance := 3, driftBudget := 2, latticeSpan := 1 },
       { stepVariance := 4, driftBudget := 3, latticeSpan := 1 }] = true := by
  unfold randomWalkDataListReady
  native_decide

structure RandomWalkWindow where
  stepVariance : ℕ
  driftBudget : ℕ
  latticeSpan : ℕ
  excursionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomWalkWindow.driftControlled (w : RandomWalkWindow) : Prop :=
  w.driftBudget ≤ w.stepVariance + w.slack

def RandomWalkWindow.excursionControlled (w : RandomWalkWindow) : Prop :=
  w.excursionBudget ≤ w.stepVariance + w.driftBudget + w.slack

def randomWalkWindowReady (w : RandomWalkWindow) : Prop :=
  0 < w.stepVariance ∧
    w.latticeSpan = 1 ∧
    w.driftControlled ∧
    w.excursionControlled

def RandomWalkWindow.certificate (w : RandomWalkWindow) : ℕ :=
  w.stepVariance + w.driftBudget + w.slack

theorem randomWalk_excursionBudget_le_certificate {w : RandomWalkWindow}
    (h : randomWalkWindowReady w) :
    w.excursionBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hexcursion⟩
  exact hexcursion

def sampleRandomWalkWindow : RandomWalkWindow :=
  { stepVariance := 4, driftBudget := 3, latticeSpan := 1, excursionBudget := 6, slack := 0 }

example : randomWalkWindowReady sampleRandomWalkWindow := by
  norm_num [randomWalkWindowReady, RandomWalkWindow.driftControlled,
    RandomWalkWindow.excursionControlled, sampleRandomWalkWindow]

example : sampleRandomWalkWindow.certificate = 7 := by
  native_decide


structure RandomWalkLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomWalkLimitSchemasBudgetCertificate.controlled
    (c : RandomWalkLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomWalkLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomWalkLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomWalkLimitSchemasBudgetCertificate.Ready
    (c : RandomWalkLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomWalkLimitSchemasBudgetCertificate.size
    (c : RandomWalkLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomWalkLimitSchemas_budgetCertificate_le_size
    (c : RandomWalkLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomWalkLimitSchemasBudgetCertificate :
    RandomWalkLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRandomWalkLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomWalkLimitSchemasBudgetCertificate.controlled,
      sampleRandomWalkLimitSchemasBudgetCertificate]
  · norm_num [RandomWalkLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomWalkLimitSchemasBudgetCertificate]

example :
    sampleRandomWalkLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomWalkLimitSchemasBudgetCertificate.size := by
  apply randomWalkLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomWalkLimitSchemasBudgetCertificate.controlled,
      sampleRandomWalkLimitSchemasBudgetCertificate]
  · norm_num [RandomWalkLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomWalkLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRandomWalkLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomWalkLimitSchemasBudgetCertificate.controlled,
      sampleRandomWalkLimitSchemasBudgetCertificate]
  · norm_num [RandomWalkLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomWalkLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomWalkLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomWalkLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RandomWalkLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomWalkLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomWalkLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomWalkLimitSchemas
