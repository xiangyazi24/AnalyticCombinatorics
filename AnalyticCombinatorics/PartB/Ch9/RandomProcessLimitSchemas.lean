import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random process limit schemas.

The finite record stores state count, transition budget, and tightness
slack.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomProcessLimitSchemas

structure RandomProcessLimitData where
  stateCount : ℕ
  transitionBudget : ℕ
  tightnessSlack : ℕ
deriving DecidableEq, Repr

def stateCountPositive (d : RandomProcessLimitData) : Prop :=
  0 < d.stateCount

def transitionBudgetControlled (d : RandomProcessLimitData) : Prop :=
  d.transitionBudget ≤ d.stateCount + d.tightnessSlack

def randomProcessLimitReady (d : RandomProcessLimitData) : Prop :=
  stateCountPositive d ∧ transitionBudgetControlled d

def randomProcessLimitBudget (d : RandomProcessLimitData) : ℕ :=
  d.stateCount + d.transitionBudget + d.tightnessSlack

theorem randomProcessLimitReady.states {d : RandomProcessLimitData}
    (h : randomProcessLimitReady d) :
    stateCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem transitionBudget_le_randomProcessBudget
    (d : RandomProcessLimitData) :
    d.transitionBudget ≤ randomProcessLimitBudget d := by
  unfold randomProcessLimitBudget
  omega

def sampleRandomProcessLimitData : RandomProcessLimitData :=
  { stateCount := 7, transitionBudget := 9, tightnessSlack := 3 }

example : randomProcessLimitReady sampleRandomProcessLimitData := by
  norm_num [randomProcessLimitReady, stateCountPositive]
  norm_num [transitionBudgetControlled, sampleRandomProcessLimitData]

example : randomProcessLimitBudget sampleRandomProcessLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for random process-limit windows. -/
def randomProcessLimitListReady
    (windows : List RandomProcessLimitData) : Bool :=
  windows.all fun d =>
    0 < d.stateCount && d.transitionBudget ≤ d.stateCount + d.tightnessSlack

theorem randomProcessLimitList_readyWindow :
    randomProcessLimitListReady
      [{ stateCount := 4, transitionBudget := 5, tightnessSlack := 1 },
       { stateCount := 7, transitionBudget := 9, tightnessSlack := 3 }] = true := by
  unfold randomProcessLimitListReady
  native_decide

structure RandomProcessLimitBudgetCertificate where
  stateCountWindow : ℕ
  transitionBudgetWindow : ℕ
  tightnessSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomProcessLimitBudgetCertificate.controlled
    (c : RandomProcessLimitBudgetCertificate) : Prop :=
  0 < c.stateCountWindow ∧
    c.transitionBudgetWindow ≤
      c.stateCountWindow + c.tightnessSlackWindow + c.slack

def RandomProcessLimitBudgetCertificate.budgetControlled
    (c : RandomProcessLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.stateCountWindow + c.transitionBudgetWindow + c.tightnessSlackWindow +
      c.slack

def RandomProcessLimitBudgetCertificate.Ready
    (c : RandomProcessLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomProcessLimitBudgetCertificate.size
    (c : RandomProcessLimitBudgetCertificate) : ℕ :=
  c.stateCountWindow + c.transitionBudgetWindow + c.tightnessSlackWindow +
    c.slack

theorem randomProcessLimit_budgetCertificate_le_size
    (c : RandomProcessLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomProcessLimitBudgetCertificate :
    RandomProcessLimitBudgetCertificate :=
  { stateCountWindow := 7
    transitionBudgetWindow := 9
    tightnessSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomProcessLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomProcessLimitBudgetCertificate.controlled,
      sampleRandomProcessLimitBudgetCertificate]
  · norm_num [RandomProcessLimitBudgetCertificate.budgetControlled,
      sampleRandomProcessLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomProcessLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomProcessLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomProcessLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomProcessLimitBudgetCertificate.controlled,
      sampleRandomProcessLimitBudgetCertificate]
  · norm_num [RandomProcessLimitBudgetCertificate.budgetControlled,
      sampleRandomProcessLimitBudgetCertificate]

example :
    sampleRandomProcessLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomProcessLimitBudgetCertificate.size := by
  apply randomProcessLimit_budgetCertificate_le_size
  constructor
  · norm_num [RandomProcessLimitBudgetCertificate.controlled,
      sampleRandomProcessLimitBudgetCertificate]
  · norm_num [RandomProcessLimitBudgetCertificate.budgetControlled,
      sampleRandomProcessLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomProcessLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomProcessLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomProcessLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomProcessLimitSchemas
