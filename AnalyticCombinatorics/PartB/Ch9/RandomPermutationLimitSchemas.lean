import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random permutation limit schemas.

The finite record stores cycle count, displacement budget, and limit
slack.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomPermutationLimitSchemas

structure RandomPermutationLimitData where
  cycleCount : ℕ
  displacementBudget : ℕ
  limitSlack : ℕ
deriving DecidableEq, Repr

def cycleCountPositive (d : RandomPermutationLimitData) : Prop :=
  0 < d.cycleCount

def displacementControlled (d : RandomPermutationLimitData) : Prop :=
  d.displacementBudget ≤ d.cycleCount + d.limitSlack

def randomPermutationLimitReady (d : RandomPermutationLimitData) : Prop :=
  cycleCountPositive d ∧ displacementControlled d

def randomPermutationLimitBudget (d : RandomPermutationLimitData) : ℕ :=
  d.cycleCount + d.displacementBudget + d.limitSlack

theorem randomPermutationLimitReady.cycles
    {d : RandomPermutationLimitData}
    (h : randomPermutationLimitReady d) :
    cycleCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem displacementBudget_le_permutationLimitBudget
    (d : RandomPermutationLimitData) :
    d.displacementBudget ≤ randomPermutationLimitBudget d := by
  unfold randomPermutationLimitBudget
  omega

def sampleRandomPermutationLimitData : RandomPermutationLimitData :=
  { cycleCount := 7, displacementBudget := 9, limitSlack := 3 }

example : randomPermutationLimitReady sampleRandomPermutationLimitData := by
  norm_num [randomPermutationLimitReady, cycleCountPositive]
  norm_num [displacementControlled, sampleRandomPermutationLimitData]

example : randomPermutationLimitBudget sampleRandomPermutationLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for random permutation-limit windows. -/
def randomPermutationLimitListReady
    (windows : List RandomPermutationLimitData) : Bool :=
  windows.all fun d =>
    0 < d.cycleCount && d.displacementBudget ≤ d.cycleCount + d.limitSlack

theorem randomPermutationLimitList_readyWindow :
    randomPermutationLimitListReady
      [{ cycleCount := 4, displacementBudget := 5, limitSlack := 1 },
       { cycleCount := 7, displacementBudget := 9, limitSlack := 3 }] = true := by
  unfold randomPermutationLimitListReady
  native_decide

structure RandomPermutationLimitBudgetCertificate where
  cycleCountWindow : ℕ
  displacementBudgetWindow : ℕ
  limitSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomPermutationLimitBudgetCertificate.controlled
    (c : RandomPermutationLimitBudgetCertificate) : Prop :=
  0 < c.cycleCountWindow ∧
    c.displacementBudgetWindow ≤ c.cycleCountWindow + c.limitSlackWindow + c.slack

def RandomPermutationLimitBudgetCertificate.budgetControlled
    (c : RandomPermutationLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.cycleCountWindow + c.displacementBudgetWindow + c.limitSlackWindow + c.slack

def RandomPermutationLimitBudgetCertificate.Ready
    (c : RandomPermutationLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomPermutationLimitBudgetCertificate.size
    (c : RandomPermutationLimitBudgetCertificate) : ℕ :=
  c.cycleCountWindow + c.displacementBudgetWindow + c.limitSlackWindow + c.slack

theorem randomPermutationLimit_budgetCertificate_le_size
    (c : RandomPermutationLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomPermutationLimitBudgetCertificate :
    RandomPermutationLimitBudgetCertificate :=
  { cycleCountWindow := 7
    displacementBudgetWindow := 9
    limitSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomPermutationLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomPermutationLimitBudgetCertificate.controlled,
      sampleRandomPermutationLimitBudgetCertificate]
  · norm_num [RandomPermutationLimitBudgetCertificate.budgetControlled,
      sampleRandomPermutationLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomPermutationLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomPermutationLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomPermutationLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomPermutationLimitBudgetCertificate.controlled,
      sampleRandomPermutationLimitBudgetCertificate]
  · norm_num [RandomPermutationLimitBudgetCertificate.budgetControlled,
      sampleRandomPermutationLimitBudgetCertificate]

example :
    sampleRandomPermutationLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomPermutationLimitBudgetCertificate.size := by
  apply randomPermutationLimit_budgetCertificate_le_size
  constructor
  · norm_num [RandomPermutationLimitBudgetCertificate.controlled,
      sampleRandomPermutationLimitBudgetCertificate]
  · norm_num [RandomPermutationLimitBudgetCertificate.budgetControlled,
      sampleRandomPermutationLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomPermutationLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomPermutationLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomPermutationLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomPermutationLimitSchemas
