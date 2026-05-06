import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite routing models.

Routes are list-encoded path lengths.  The definitions record total route
cost, hop count, and budget checks.
-/

namespace AnalyticCombinatorics.AppA.FiniteRoutingModels

def routeCost (segments : List ℕ) : ℕ :=
  segments.sum

def hopCount (segments : List ℕ) : ℕ :=
  segments.length

def routeWithinBudget (segments : List ℕ) (budget : ℕ) : Prop :=
  routeCost segments ≤ budget

theorem routeCost_cons (x : ℕ) (segments : List ℕ) :
    routeCost (x :: segments) = x + routeCost segments := by
  simp [routeCost]

theorem hopCount_cons (x : ℕ) (segments : List ℕ) :
    hopCount (x :: segments) = hopCount segments + 1 := by
  simp [hopCount]

theorem routeWithinBudget_mono {segments : List ℕ} {a b : ℕ}
    (h : routeWithinBudget segments a) (hab : a ≤ b) :
    routeWithinBudget segments b := by
  unfold routeWithinBudget at *
  omega

def sampleRoute : List ℕ :=
  [2, 3, 5, 1]

example : routeCost sampleRoute = 11 := by
  native_decide

example : hopCount sampleRoute = 4 := by
  native_decide

example : routeWithinBudget sampleRoute 12 := by
  norm_num [routeWithinBudget, routeCost, sampleRoute]

structure RoutingWindow where
  hops : ℕ
  routeMass : ℕ
  budget : ℕ
  detourSlack : ℕ
deriving DecidableEq, Repr

def RoutingWindow.costControlled (w : RoutingWindow) : Prop :=
  w.routeMass ≤ w.budget + w.detourSlack

def RoutingWindow.hopControlled (w : RoutingWindow) : Prop :=
  w.hops ≤ w.routeMass + w.detourSlack

def RoutingWindow.ready (w : RoutingWindow) : Prop :=
  w.costControlled ∧ w.hopControlled

def RoutingWindow.certificate (w : RoutingWindow) : ℕ :=
  w.hops + w.routeMass + w.budget + w.detourSlack

theorem routeMass_le_certificate (w : RoutingWindow) :
    w.routeMass ≤ w.certificate := by
  unfold RoutingWindow.certificate
  omega

def sampleRoutingWindow : RoutingWindow :=
  { hops := 4, routeMass := 11, budget := 12, detourSlack := 0 }

example : sampleRoutingWindow.ready := by
  norm_num [sampleRoutingWindow, RoutingWindow.ready, RoutingWindow.costControlled,
    RoutingWindow.hopControlled]


structure FiniteRoutingModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteRoutingModelsBudgetCertificate.controlled
    (c : FiniteRoutingModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteRoutingModelsBudgetCertificate.budgetControlled
    (c : FiniteRoutingModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteRoutingModelsBudgetCertificate.Ready
    (c : FiniteRoutingModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteRoutingModelsBudgetCertificate.size
    (c : FiniteRoutingModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteRoutingModels_budgetCertificate_le_size
    (c : FiniteRoutingModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteRoutingModelsBudgetCertificate :
    FiniteRoutingModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteRoutingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRoutingModelsBudgetCertificate.controlled,
      sampleFiniteRoutingModelsBudgetCertificate]
  · norm_num [FiniteRoutingModelsBudgetCertificate.budgetControlled,
      sampleFiniteRoutingModelsBudgetCertificate]

example :
    sampleFiniteRoutingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRoutingModelsBudgetCertificate.size := by
  apply finiteRoutingModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteRoutingModelsBudgetCertificate.controlled,
      sampleFiniteRoutingModelsBudgetCertificate]
  · norm_num [FiniteRoutingModelsBudgetCertificate.budgetControlled,
      sampleFiniteRoutingModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteRoutingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRoutingModelsBudgetCertificate.controlled,
      sampleFiniteRoutingModelsBudgetCertificate]
  · norm_num [FiniteRoutingModelsBudgetCertificate.budgetControlled,
      sampleFiniteRoutingModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteRoutingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRoutingModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteRoutingModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteRoutingModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteRoutingModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteRoutingModels
