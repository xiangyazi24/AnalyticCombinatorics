import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite resource models.

Resources are represented by natural budgets.  The file records allocation,
capacity, and slack calculations used by finite combinatorial models.
-/

namespace AnalyticCombinatorics.AppA.FiniteResourceModels

structure ResourceDatum where
  demand : ℕ
  capacity : ℕ
  reserve : ℕ
deriving DecidableEq, Repr

def demandCovered (d : ResourceDatum) : Prop :=
  d.demand ≤ d.capacity

def reserveCovered (d : ResourceDatum) : Prop :=
  d.demand + d.reserve ≤ d.capacity

def resourceSlack (d : ResourceDatum) : ℕ :=
  d.capacity - d.demand

theorem reserveCovered.demand {d : ResourceDatum}
    (h : reserveCovered d) :
    demandCovered d := by
  unfold reserveCovered demandCovered at *
  omega

theorem resourceSlack_add {d : ResourceDatum}
    (h : demandCovered d) :
    resourceSlack d + d.demand = d.capacity := by
  unfold resourceSlack demandCovered at *
  omega

def sampleResource : ResourceDatum :=
  { demand := 6, capacity := 10, reserve := 3 }

example : reserveCovered sampleResource := by
  norm_num [reserveCovered, sampleResource]

example : resourceSlack sampleResource = 4 := by
  native_decide

structure ResourceWindow where
  demand : ℕ
  capacity : ℕ
  reserve : ℕ
  allocated : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ResourceWindow.capacityReady (w : ResourceWindow) : Prop :=
  w.demand + w.reserve ≤ w.capacity + w.slack

def ResourceWindow.allocationControlled (w : ResourceWindow) : Prop :=
  w.allocated ≤ w.capacity + w.slack

def ResourceWindow.ready (w : ResourceWindow) : Prop :=
  w.capacityReady ∧ w.allocationControlled

def ResourceWindow.certificate (w : ResourceWindow) : ℕ :=
  w.demand + w.capacity + w.reserve + w.allocated + w.slack

theorem allocated_le_certificate (w : ResourceWindow) :
    w.allocated ≤ w.certificate := by
  unfold ResourceWindow.certificate
  omega

def sampleResourceWindow : ResourceWindow :=
  { demand := 6, capacity := 10, reserve := 3, allocated := 8, slack := 0 }

example : sampleResourceWindow.ready := by
  norm_num [sampleResourceWindow, ResourceWindow.ready,
    ResourceWindow.capacityReady, ResourceWindow.allocationControlled]


structure FiniteResourceModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteResourceModelsBudgetCertificate.controlled
    (c : FiniteResourceModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteResourceModelsBudgetCertificate.budgetControlled
    (c : FiniteResourceModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteResourceModelsBudgetCertificate.Ready
    (c : FiniteResourceModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteResourceModelsBudgetCertificate.size
    (c : FiniteResourceModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteResourceModels_budgetCertificate_le_size
    (c : FiniteResourceModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteResourceModelsBudgetCertificate :
    FiniteResourceModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteResourceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteResourceModelsBudgetCertificate.controlled,
      sampleFiniteResourceModelsBudgetCertificate]
  · norm_num [FiniteResourceModelsBudgetCertificate.budgetControlled,
      sampleFiniteResourceModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteResourceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteResourceModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteResourceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteResourceModelsBudgetCertificate.controlled,
      sampleFiniteResourceModelsBudgetCertificate]
  · norm_num [FiniteResourceModelsBudgetCertificate.budgetControlled,
      sampleFiniteResourceModelsBudgetCertificate]

example :
    sampleFiniteResourceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteResourceModelsBudgetCertificate.size := by
  apply finiteResourceModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteResourceModelsBudgetCertificate.controlled,
      sampleFiniteResourceModelsBudgetCertificate]
  · norm_num [FiniteResourceModelsBudgetCertificate.budgetControlled,
      sampleFiniteResourceModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteResourceModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteResourceModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteResourceModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteResourceModels
