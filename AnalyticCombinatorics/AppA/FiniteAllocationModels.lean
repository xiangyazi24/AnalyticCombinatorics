import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite allocation models.

Allocations are represented by lists of bin loads.  This file records total
mass, bin count, and capacity checks.
-/

namespace AnalyticCombinatorics.AppA.FiniteAllocationModels

def allocationMass (loads : List ℕ) : ℕ :=
  loads.sum

def allocationBins (loads : List ℕ) : ℕ :=
  loads.length

def allocationWithinCapacity (loads : List ℕ) (capacity : ℕ) : Prop :=
  allocationMass loads ≤ capacity

def allocationSlack (loads : List ℕ) (capacity : ℕ) : ℕ :=
  capacity - allocationMass loads

theorem allocationMass_cons (x : ℕ) (loads : List ℕ) :
    allocationMass (x :: loads) = x + allocationMass loads := by
  simp [allocationMass]

theorem allocationBins_cons (x : ℕ) (loads : List ℕ) :
    allocationBins (x :: loads) = allocationBins loads + 1 := by
  simp [allocationBins]

theorem allocationSlack_add {loads : List ℕ} {capacity : ℕ}
    (h : allocationWithinCapacity loads capacity) :
    allocationSlack loads capacity + allocationMass loads = capacity := by
  unfold allocationSlack allocationWithinCapacity at *
  omega

def sampleAllocation : List ℕ :=
  [4, 0, 3, 2]

example : allocationMass sampleAllocation = 9 := by
  native_decide

example : allocationBins sampleAllocation = 4 := by
  native_decide

example : allocationWithinCapacity sampleAllocation 10 := by
  norm_num [allocationWithinCapacity, allocationMass, sampleAllocation]

structure AllocationWindow where
  bins : ℕ
  mass : ℕ
  capacity : ℕ
  maxLoad : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AllocationWindow.capacityReady (w : AllocationWindow) : Prop :=
  w.mass ≤ w.capacity + w.slack

def AllocationWindow.binControlled (w : AllocationWindow) : Prop :=
  w.mass ≤ w.bins * w.maxLoad + w.slack

def AllocationWindow.ready (w : AllocationWindow) : Prop :=
  w.capacityReady ∧ w.binControlled

def AllocationWindow.certificate (w : AllocationWindow) : ℕ :=
  w.bins + w.mass + w.capacity + w.maxLoad + w.slack

theorem mass_le_certificate (w : AllocationWindow) :
    w.mass ≤ w.certificate := by
  unfold AllocationWindow.certificate
  omega

def sampleAllocationWindow : AllocationWindow :=
  { bins := 4, mass := 9, capacity := 10, maxLoad := 4, slack := 0 }

example : sampleAllocationWindow.ready := by
  norm_num [sampleAllocationWindow, AllocationWindow.ready,
    AllocationWindow.capacityReady, AllocationWindow.binControlled]


structure FiniteAllocationModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteAllocationModelsBudgetCertificate.controlled
    (c : FiniteAllocationModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteAllocationModelsBudgetCertificate.budgetControlled
    (c : FiniteAllocationModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteAllocationModelsBudgetCertificate.Ready
    (c : FiniteAllocationModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteAllocationModelsBudgetCertificate.size
    (c : FiniteAllocationModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteAllocationModels_budgetCertificate_le_size
    (c : FiniteAllocationModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteAllocationModelsBudgetCertificate :
    FiniteAllocationModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteAllocationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteAllocationModelsBudgetCertificate.controlled,
      sampleFiniteAllocationModelsBudgetCertificate]
  · norm_num [FiniteAllocationModelsBudgetCertificate.budgetControlled,
      sampleFiniteAllocationModelsBudgetCertificate]

example :
    sampleFiniteAllocationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteAllocationModelsBudgetCertificate.size := by
  apply finiteAllocationModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteAllocationModelsBudgetCertificate.controlled,
      sampleFiniteAllocationModelsBudgetCertificate]
  · norm_num [FiniteAllocationModelsBudgetCertificate.budgetControlled,
      sampleFiniteAllocationModelsBudgetCertificate]

/-- Finite executable readiness audit for finite-allocation certificates. -/
def finiteAllocationModelsBudgetCertificateListReady
    (data : List FiniteAllocationModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteAllocationModelsBudgetCertificateList_readyWindow :
    finiteAllocationModelsBudgetCertificateListReady
      [sampleFiniteAllocationModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold finiteAllocationModelsBudgetCertificateListReady
    sampleFiniteAllocationModelsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteAllocationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteAllocationModelsBudgetCertificate.controlled,
      sampleFiniteAllocationModelsBudgetCertificate]
  · norm_num [FiniteAllocationModelsBudgetCertificate.budgetControlled,
      sampleFiniteAllocationModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteAllocationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteAllocationModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FiniteAllocationModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteAllocationModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFiniteAllocationModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FiniteAllocationModels
