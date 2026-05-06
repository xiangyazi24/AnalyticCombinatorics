import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite load-balancing models.

Loads are list-encoded bin weights.  This file records total load, bin
count, and capacity checks.
-/

namespace AnalyticCombinatorics.AppA.FiniteLoadBalancingModels

def totalLoad (loads : List ℕ) : ℕ :=
  loads.sum

def binCount (loads : List ℕ) : ℕ :=
  loads.length

def loadWithinCapacity (loads : List ℕ) (capacity : ℕ) : Prop :=
  totalLoad loads ≤ capacity

def overload (loads : List ℕ) (capacity : ℕ) : ℕ :=
  totalLoad loads - capacity

theorem totalLoad_cons (x : ℕ) (loads : List ℕ) :
    totalLoad (x :: loads) = x + totalLoad loads := by
  simp [totalLoad]

theorem binCount_cons (x : ℕ) (loads : List ℕ) :
    binCount (x :: loads) = binCount loads + 1 := by
  simp [binCount]

theorem loadWithinCapacity_mono {loads : List ℕ} {a b : ℕ}
    (h : loadWithinCapacity loads a) (hab : a ≤ b) :
    loadWithinCapacity loads b := by
  unfold loadWithinCapacity at *
  omega

def sampleLoads : List ℕ :=
  [3, 5, 2, 4]

example : totalLoad sampleLoads = 14 := by
  native_decide

example : binCount sampleLoads = 4 := by
  native_decide

example : loadWithinCapacity sampleLoads 20 := by
  norm_num [loadWithinCapacity, totalLoad, sampleLoads]

structure LoadBalancingWindow where
  bins : ℕ
  totalLoad : ℕ
  capacity : ℕ
  maxBinLoad : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LoadBalancingWindow.capacityReady (w : LoadBalancingWindow) : Prop :=
  w.totalLoad ≤ w.capacity + w.slack

def LoadBalancingWindow.balanceControlled (w : LoadBalancingWindow) : Prop :=
  w.totalLoad ≤ w.bins * w.maxBinLoad + w.slack

def LoadBalancingWindow.ready (w : LoadBalancingWindow) : Prop :=
  w.capacityReady ∧ w.balanceControlled

def LoadBalancingWindow.certificate (w : LoadBalancingWindow) : ℕ :=
  w.bins + w.totalLoad + w.capacity + w.maxBinLoad + w.slack

theorem maxBinLoad_le_certificate (w : LoadBalancingWindow) :
    w.maxBinLoad ≤ w.certificate := by
  unfold LoadBalancingWindow.certificate
  omega

def sampleLoadBalancingWindow : LoadBalancingWindow :=
  { bins := 4, totalLoad := 14, capacity := 20, maxBinLoad := 5, slack := 0 }

example : sampleLoadBalancingWindow.ready := by
  norm_num [sampleLoadBalancingWindow, LoadBalancingWindow.ready,
    LoadBalancingWindow.capacityReady, LoadBalancingWindow.balanceControlled]


structure FiniteLoadBalancingModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteLoadBalancingModelsBudgetCertificate.controlled
    (c : FiniteLoadBalancingModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteLoadBalancingModelsBudgetCertificate.budgetControlled
    (c : FiniteLoadBalancingModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteLoadBalancingModelsBudgetCertificate.Ready
    (c : FiniteLoadBalancingModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteLoadBalancingModelsBudgetCertificate.size
    (c : FiniteLoadBalancingModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteLoadBalancingModels_budgetCertificate_le_size
    (c : FiniteLoadBalancingModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteLoadBalancingModelsBudgetCertificate :
    FiniteLoadBalancingModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteLoadBalancingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLoadBalancingModelsBudgetCertificate.controlled,
      sampleFiniteLoadBalancingModelsBudgetCertificate]
  · norm_num [FiniteLoadBalancingModelsBudgetCertificate.budgetControlled,
      sampleFiniteLoadBalancingModelsBudgetCertificate]

example :
    sampleFiniteLoadBalancingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLoadBalancingModelsBudgetCertificate.size := by
  apply finiteLoadBalancingModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteLoadBalancingModelsBudgetCertificate.controlled,
      sampleFiniteLoadBalancingModelsBudgetCertificate]
  · norm_num [FiniteLoadBalancingModelsBudgetCertificate.budgetControlled,
      sampleFiniteLoadBalancingModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteLoadBalancingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLoadBalancingModelsBudgetCertificate.controlled,
      sampleFiniteLoadBalancingModelsBudgetCertificate]
  · norm_num [FiniteLoadBalancingModelsBudgetCertificate.budgetControlled,
      sampleFiniteLoadBalancingModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteLoadBalancingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLoadBalancingModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteLoadBalancingModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteLoadBalancingModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteLoadBalancingModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteLoadBalancingModels
