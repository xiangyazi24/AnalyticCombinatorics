import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite rank models.

The module records rank/nullity-style arithmetic used in finite linear
algebra examples without importing project-local matrix files.
-/

namespace AnalyticCombinatorics.AppA.FiniteRankModels

structure RankDatum where
  columns : ℕ
  rank : ℕ
  kernelDimension : ℕ
deriving DecidableEq, Repr

def rankNullityBalanced (d : RankDatum) : Prop :=
  d.rank + d.kernelDimension = d.columns

def rankBounded (d : RankDatum) : Prop :=
  d.rank ≤ d.columns

def nullityBounded (d : RankDatum) : Prop :=
  d.kernelDimension ≤ d.columns

theorem rankNullityBalanced.rank_bound {d : RankDatum}
    (h : rankNullityBalanced d) :
    rankBounded d := by
  unfold rankNullityBalanced rankBounded at *
  omega

theorem rankNullityBalanced.nullity_bound {d : RankDatum}
    (h : rankNullityBalanced d) :
    nullityBounded d := by
  unfold rankNullityBalanced nullityBounded at *
  omega

def sampleRank : RankDatum :=
  { columns := 8, rank := 5, kernelDimension := 3 }

example : rankNullityBalanced sampleRank := by
  norm_num [rankNullityBalanced, sampleRank]

example : rankBounded sampleRank := by
  norm_num [rankBounded, sampleRank]

structure RankWindow where
  columns : ℕ
  rank : ℕ
  kernelDimension : ℕ
  rankSlack : ℕ
deriving DecidableEq, Repr

def RankWindow.balanced (w : RankWindow) : Prop :=
  w.rank + w.kernelDimension ≤ w.columns + w.rankSlack

def RankWindow.rankControlled (w : RankWindow) : Prop :=
  w.rank ≤ w.columns

def RankWindow.ready (w : RankWindow) : Prop :=
  w.balanced ∧ w.rankControlled

def RankWindow.certificate (w : RankWindow) : ℕ :=
  w.columns + w.rank + w.kernelDimension + w.rankSlack

theorem kernelDimension_le_certificate (w : RankWindow) :
    w.kernelDimension ≤ w.certificate := by
  unfold RankWindow.certificate
  omega

def sampleRankWindow : RankWindow :=
  { columns := 8, rank := 5, kernelDimension := 3, rankSlack := 0 }

example : sampleRankWindow.ready := by
  norm_num [sampleRankWindow, RankWindow.ready, RankWindow.balanced,
    RankWindow.rankControlled]


structure FiniteRankModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteRankModelsBudgetCertificate.controlled
    (c : FiniteRankModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteRankModelsBudgetCertificate.budgetControlled
    (c : FiniteRankModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteRankModelsBudgetCertificate.Ready
    (c : FiniteRankModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteRankModelsBudgetCertificate.size
    (c : FiniteRankModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteRankModels_budgetCertificate_le_size
    (c : FiniteRankModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteRankModelsBudgetCertificate :
    FiniteRankModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteRankModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRankModelsBudgetCertificate.controlled,
      sampleFiniteRankModelsBudgetCertificate]
  · norm_num [FiniteRankModelsBudgetCertificate.budgetControlled,
      sampleFiniteRankModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteRankModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRankModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteRankModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRankModelsBudgetCertificate.controlled,
      sampleFiniteRankModelsBudgetCertificate]
  · norm_num [FiniteRankModelsBudgetCertificate.budgetControlled,
      sampleFiniteRankModelsBudgetCertificate]

example :
    sampleFiniteRankModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRankModelsBudgetCertificate.size := by
  apply finiteRankModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteRankModelsBudgetCertificate.controlled,
      sampleFiniteRankModelsBudgetCertificate]
  · norm_num [FiniteRankModelsBudgetCertificate.budgetControlled,
      sampleFiniteRankModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteRankModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteRankModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteRankModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteRankModels
