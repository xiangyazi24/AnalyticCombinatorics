import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite matroid models.

This file keeps rank, ground-set, and circuit budgets for finite matroid
bookkeeping.
-/

namespace AnalyticCombinatorics.AppA.FiniteMatroidModels

structure MatroidData where
  groundSize : ℕ
  rankBound : ℕ
  circuitBudget : ℕ
deriving DecidableEq, Repr

def groundNonempty (d : MatroidData) : Prop :=
  0 < d.groundSize

def rankControlled (d : MatroidData) : Prop :=
  d.rankBound ≤ d.groundSize

def matroidReady (d : MatroidData) : Prop :=
  groundNonempty d ∧ rankControlled d

def matroidBudget (d : MatroidData) : ℕ :=
  d.groundSize + d.rankBound + d.circuitBudget

theorem matroidReady.ground {d : MatroidData} (h : matroidReady d) :
    groundNonempty d ∧ rankControlled d ∧ d.rankBound ≤ matroidBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold matroidBudget
  omega

theorem rankBound_le_matroidBudget (d : MatroidData) :
    d.rankBound ≤ matroidBudget d := by
  unfold matroidBudget
  omega

def sampleMatroidData : MatroidData :=
  { groundSize := 9, rankBound := 4, circuitBudget := 6 }

example : matroidReady sampleMatroidData := by
  norm_num [matroidReady, groundNonempty]
  norm_num [rankControlled, sampleMatroidData]

example : matroidBudget sampleMatroidData = 19 := by
  native_decide

structure MatroidWindow where
  groundSize : ℕ
  rankBound : ℕ
  circuitBudget : ℕ
  basisBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MatroidWindow.rankControlled (w : MatroidWindow) : Prop :=
  w.rankBound ≤ w.groundSize

def MatroidWindow.basisControlled (w : MatroidWindow) : Prop :=
  w.basisBudget ≤ w.groundSize + w.rankBound + w.circuitBudget + w.slack

def matroidWindowReady (w : MatroidWindow) : Prop :=
  0 < w.groundSize ∧
    w.rankControlled ∧
    w.basisControlled

def MatroidWindow.certificate (w : MatroidWindow) : ℕ :=
  w.groundSize + w.rankBound + w.circuitBudget + w.slack

theorem matroid_basisBudget_le_certificate {w : MatroidWindow}
    (h : matroidWindowReady w) :
    w.basisBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hbasis⟩
  exact hbasis

def sampleMatroidWindow : MatroidWindow :=
  { groundSize := 9, rankBound := 4, circuitBudget := 6, basisBudget := 17, slack := 0 }

example : matroidWindowReady sampleMatroidWindow := by
  norm_num [matroidWindowReady, MatroidWindow.rankControlled, MatroidWindow.basisControlled,
    sampleMatroidWindow]

example : sampleMatroidWindow.certificate = 19 := by
  native_decide


structure FiniteMatroidModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteMatroidModelsBudgetCertificate.controlled
    (c : FiniteMatroidModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteMatroidModelsBudgetCertificate.budgetControlled
    (c : FiniteMatroidModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteMatroidModelsBudgetCertificate.Ready
    (c : FiniteMatroidModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteMatroidModelsBudgetCertificate.size
    (c : FiniteMatroidModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteMatroidModels_budgetCertificate_le_size
    (c : FiniteMatroidModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteMatroidModelsBudgetCertificate :
    FiniteMatroidModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteMatroidModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteMatroidModelsBudgetCertificate.controlled,
      sampleFiniteMatroidModelsBudgetCertificate]
  · norm_num [FiniteMatroidModelsBudgetCertificate.budgetControlled,
      sampleFiniteMatroidModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteMatroidModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteMatroidModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteMatroidModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteMatroidModelsBudgetCertificate.controlled,
      sampleFiniteMatroidModelsBudgetCertificate]
  · norm_num [FiniteMatroidModelsBudgetCertificate.budgetControlled,
      sampleFiniteMatroidModelsBudgetCertificate]

example :
    sampleFiniteMatroidModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteMatroidModelsBudgetCertificate.size := by
  apply finiteMatroidModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteMatroidModelsBudgetCertificate.controlled,
      sampleFiniteMatroidModelsBudgetCertificate]
  · norm_num [FiniteMatroidModelsBudgetCertificate.budgetControlled,
      sampleFiniteMatroidModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteMatroidModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteMatroidModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteMatroidModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteMatroidModels
