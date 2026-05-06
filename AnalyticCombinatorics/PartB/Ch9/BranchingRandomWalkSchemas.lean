import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Branching random walk schema bookkeeping.

The finite data records branching factor, displacement variance, and drift
budget.
-/

namespace AnalyticCombinatorics.PartB.Ch9.BranchingRandomWalkSchemas

structure BranchingRandomWalkData where
  branchingFactor : ℕ
  displacementVariance : ℕ
  driftBudget : ℕ
deriving DecidableEq, Repr

def nontrivialBranching (d : BranchingRandomWalkData) : Prop :=
  1 < d.branchingFactor

def positiveDisplacementVariance (d : BranchingRandomWalkData) : Prop :=
  0 < d.displacementVariance

def branchingRandomWalkReady (d : BranchingRandomWalkData) : Prop :=
  nontrivialBranching d ∧ positiveDisplacementVariance d

def branchingWalkBudget (d : BranchingRandomWalkData) : ℕ :=
  d.branchingFactor + d.displacementVariance + d.driftBudget

theorem branchingRandomWalkReady.branching {d : BranchingRandomWalkData}
    (h : branchingRandomWalkReady d) :
    nontrivialBranching d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem branchingFactor_le_budget (d : BranchingRandomWalkData) :
    d.branchingFactor ≤ branchingWalkBudget d := by
  unfold branchingWalkBudget
  omega

def sampleBranchingRandomWalk : BranchingRandomWalkData :=
  { branchingFactor := 3, displacementVariance := 5, driftBudget := 2 }

example : branchingRandomWalkReady sampleBranchingRandomWalk := by
  norm_num
    [branchingRandomWalkReady, nontrivialBranching, positiveDisplacementVariance,
      sampleBranchingRandomWalk]

example : branchingWalkBudget sampleBranchingRandomWalk = 10 := by
  native_decide

/-- Finite executable readiness audit for branching random-walk windows. -/
def branchingRandomWalkListReady
    (windows : List BranchingRandomWalkData) : Bool :=
  windows.all fun d =>
    1 < d.branchingFactor &&
      0 < d.displacementVariance &&
        d.driftBudget ≤ d.branchingFactor + d.displacementVariance

theorem branchingRandomWalkList_readyWindow :
    branchingRandomWalkListReady
      [{ branchingFactor := 2, displacementVariance := 3, driftBudget := 1 },
       { branchingFactor := 3, displacementVariance := 5, driftBudget := 2 }] = true := by
  unfold branchingRandomWalkListReady
  native_decide

structure BranchingRandomWalkBudgetCertificate where
  branchingFactorWindow : ℕ
  displacementVarianceWindow : ℕ
  driftBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BranchingRandomWalkBudgetCertificate.controlled
    (c : BranchingRandomWalkBudgetCertificate) : Prop :=
  1 < c.branchingFactorWindow ∧
    0 < c.displacementVarianceWindow ∧
      c.driftBudgetWindow ≤
        c.branchingFactorWindow + c.displacementVarianceWindow + c.slack

def BranchingRandomWalkBudgetCertificate.budgetControlled
    (c : BranchingRandomWalkBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.branchingFactorWindow + c.displacementVarianceWindow + c.driftBudgetWindow +
      c.slack

def BranchingRandomWalkBudgetCertificate.Ready
    (c : BranchingRandomWalkBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BranchingRandomWalkBudgetCertificate.size
    (c : BranchingRandomWalkBudgetCertificate) : ℕ :=
  c.branchingFactorWindow + c.displacementVarianceWindow + c.driftBudgetWindow +
    c.slack

theorem branchingRandomWalk_budgetCertificate_le_size
    (c : BranchingRandomWalkBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBranchingRandomWalkBudgetCertificate :
    BranchingRandomWalkBudgetCertificate :=
  { branchingFactorWindow := 3
    displacementVarianceWindow := 5
    driftBudgetWindow := 2
    certificateBudgetWindow := 11
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBranchingRandomWalkBudgetCertificate.Ready := by
  constructor
  · norm_num [BranchingRandomWalkBudgetCertificate.controlled,
      sampleBranchingRandomWalkBudgetCertificate]
  · norm_num [BranchingRandomWalkBudgetCertificate.budgetControlled,
      sampleBranchingRandomWalkBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBranchingRandomWalkBudgetCertificate.certificateBudgetWindow ≤
      sampleBranchingRandomWalkBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBranchingRandomWalkBudgetCertificate.Ready := by
  constructor
  · norm_num [BranchingRandomWalkBudgetCertificate.controlled,
      sampleBranchingRandomWalkBudgetCertificate]
  · norm_num [BranchingRandomWalkBudgetCertificate.budgetControlled,
      sampleBranchingRandomWalkBudgetCertificate]

example :
    sampleBranchingRandomWalkBudgetCertificate.certificateBudgetWindow ≤
      sampleBranchingRandomWalkBudgetCertificate.size := by
  apply branchingRandomWalk_budgetCertificate_le_size
  constructor
  · norm_num [BranchingRandomWalkBudgetCertificate.controlled,
      sampleBranchingRandomWalkBudgetCertificate]
  · norm_num [BranchingRandomWalkBudgetCertificate.budgetControlled,
      sampleBranchingRandomWalkBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List BranchingRandomWalkBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBranchingRandomWalkBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleBranchingRandomWalkBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.BranchingRandomWalkSchemas
