import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite order ideal models.

The record tracks ambient size, ideal size, and boundary budget for
finite poset ideal estimates.
-/

namespace AnalyticCombinatorics.AppA.FiniteOrderIdealModels

structure OrderIdealData where
  ambientSize : ℕ
  idealSize : ℕ
  boundaryBudget : ℕ
deriving DecidableEq, Repr

def ambientNonempty (d : OrderIdealData) : Prop :=
  0 < d.ambientSize

def idealControlled (d : OrderIdealData) : Prop :=
  d.idealSize ≤ d.ambientSize

def orderIdealReady (d : OrderIdealData) : Prop :=
  ambientNonempty d ∧ idealControlled d

def orderIdealBudget (d : OrderIdealData) : ℕ :=
  d.ambientSize + d.idealSize + d.boundaryBudget

theorem orderIdealReady.ambient {d : OrderIdealData}
    (h : orderIdealReady d) :
    ambientNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem idealSize_le_orderIdealBudget (d : OrderIdealData) :
    d.idealSize ≤ orderIdealBudget d := by
  unfold orderIdealBudget
  omega

def sampleOrderIdealData : OrderIdealData :=
  { ambientSize := 12, idealSize := 5, boundaryBudget := 4 }

example : orderIdealReady sampleOrderIdealData := by
  norm_num [orderIdealReady, ambientNonempty]
  norm_num [idealControlled, sampleOrderIdealData]

example : orderIdealBudget sampleOrderIdealData = 21 := by
  native_decide

structure OrderIdealWindow where
  ambientSize : ℕ
  idealSize : ℕ
  boundaryBudget : ℕ
  closureBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def OrderIdealWindow.idealControlled (w : OrderIdealWindow) : Prop :=
  w.idealSize ≤ w.ambientSize

def OrderIdealWindow.closureControlled (w : OrderIdealWindow) : Prop :=
  w.closureBudget ≤ w.ambientSize + w.idealSize + w.boundaryBudget + w.slack

def orderIdealWindowReady (w : OrderIdealWindow) : Prop :=
  0 < w.ambientSize ∧
    w.idealControlled ∧
    w.closureControlled

def OrderIdealWindow.certificate (w : OrderIdealWindow) : ℕ :=
  w.ambientSize + w.idealSize + w.boundaryBudget + w.slack

theorem orderIdeal_closureBudget_le_certificate {w : OrderIdealWindow}
    (h : orderIdealWindowReady w) :
    w.closureBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hclosure⟩
  exact hclosure

def sampleOrderIdealWindow : OrderIdealWindow :=
  { ambientSize := 12, idealSize := 5, boundaryBudget := 4, closureBudget := 20, slack := 0 }

example : orderIdealWindowReady sampleOrderIdealWindow := by
  norm_num [orderIdealWindowReady, OrderIdealWindow.idealControlled,
    OrderIdealWindow.closureControlled, sampleOrderIdealWindow]

example : sampleOrderIdealWindow.certificate = 21 := by
  native_decide


structure FiniteOrderIdealModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteOrderIdealModelsBudgetCertificate.controlled
    (c : FiniteOrderIdealModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteOrderIdealModelsBudgetCertificate.budgetControlled
    (c : FiniteOrderIdealModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteOrderIdealModelsBudgetCertificate.Ready
    (c : FiniteOrderIdealModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteOrderIdealModelsBudgetCertificate.size
    (c : FiniteOrderIdealModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteOrderIdealModels_budgetCertificate_le_size
    (c : FiniteOrderIdealModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteOrderIdealModelsBudgetCertificate :
    FiniteOrderIdealModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteOrderIdealModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteOrderIdealModelsBudgetCertificate.controlled,
      sampleFiniteOrderIdealModelsBudgetCertificate]
  · norm_num [FiniteOrderIdealModelsBudgetCertificate.budgetControlled,
      sampleFiniteOrderIdealModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteOrderIdealModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteOrderIdealModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteOrderIdealModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteOrderIdealModelsBudgetCertificate.controlled,
      sampleFiniteOrderIdealModelsBudgetCertificate]
  · norm_num [FiniteOrderIdealModelsBudgetCertificate.budgetControlled,
      sampleFiniteOrderIdealModelsBudgetCertificate]

example :
    sampleFiniteOrderIdealModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteOrderIdealModelsBudgetCertificate.size := by
  apply finiteOrderIdealModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteOrderIdealModelsBudgetCertificate.controlled,
      sampleFiniteOrderIdealModelsBudgetCertificate]
  · norm_num [FiniteOrderIdealModelsBudgetCertificate.budgetControlled,
      sampleFiniteOrderIdealModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteOrderIdealModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteOrderIdealModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteOrderIdealModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteOrderIdealModels
