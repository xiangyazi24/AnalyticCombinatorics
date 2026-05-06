import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Moment Tauberian schema bookkeeping.

The finite record tracks moment order, moment budget, and tail error.
-/

namespace AnalyticCombinatorics.AppC.MomentTauberianSchemas

structure MomentTauberianData where
  momentOrder : ℕ
  momentBudget : ℕ
  tailError : ℕ
deriving DecidableEq, Repr

def positiveMomentOrder (d : MomentTauberianData) : Prop :=
  0 < d.momentOrder

def tailErrorControlled (d : MomentTauberianData) : Prop :=
  d.tailError ≤ d.momentBudget

def momentTauberianReady (d : MomentTauberianData) : Prop :=
  positiveMomentOrder d ∧ tailErrorControlled d

def totalMomentBudget (d : MomentTauberianData) : ℕ :=
  d.momentOrder + d.momentBudget + d.tailError

theorem momentTauberianReady.tail {d : MomentTauberianData}
    (h : momentTauberianReady d) :
    tailErrorControlled d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem momentOrder_le_total (d : MomentTauberianData) :
    d.momentOrder ≤ totalMomentBudget d := by
  unfold totalMomentBudget
  omega

def sampleMomentTauberian : MomentTauberianData :=
  { momentOrder := 3, momentBudget := 8, tailError := 2 }

example : momentTauberianReady sampleMomentTauberian := by
  norm_num [momentTauberianReady, positiveMomentOrder, tailErrorControlled, sampleMomentTauberian]

example : totalMomentBudget sampleMomentTauberian = 13 := by
  native_decide

structure MomentTauberianWindow where
  momentOrder : ℕ
  momentBudget : ℕ
  tailError : ℕ
  normalizationBudget : ℕ
deriving DecidableEq, Repr

def MomentTauberianWindow.orderReady (w : MomentTauberianWindow) : Prop :=
  0 < w.momentOrder

def MomentTauberianWindow.tailControlled (w : MomentTauberianWindow) : Prop :=
  w.tailError ≤ w.momentBudget + w.normalizationBudget

def MomentTauberianWindow.ready (w : MomentTauberianWindow) : Prop :=
  w.orderReady ∧ w.tailControlled

def MomentTauberianWindow.certificate (w : MomentTauberianWindow) : ℕ :=
  w.momentOrder + w.momentBudget + w.tailError + w.normalizationBudget

theorem momentBudget_le_certificate (w : MomentTauberianWindow) :
    w.momentBudget ≤ w.certificate := by
  unfold MomentTauberianWindow.certificate
  omega

def sampleMomentTauberianWindow : MomentTauberianWindow :=
  { momentOrder := 3, momentBudget := 8, tailError := 2, normalizationBudget := 1 }

example : sampleMomentTauberianWindow.ready := by
  norm_num [sampleMomentTauberianWindow, MomentTauberianWindow.ready,
    MomentTauberianWindow.orderReady, MomentTauberianWindow.tailControlled]

structure MomentTauberianRefinementWindow where
  orderWindow : ℕ
  momentWindow : ℕ
  tailWindow : ℕ
  momentBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MomentTauberianRefinementWindow.tailControlled
    (w : MomentTauberianRefinementWindow) : Prop :=
  w.tailWindow ≤ w.momentWindow + w.slack

def momentTauberianRefinementWindowReady
    (w : MomentTauberianRefinementWindow) : Prop :=
  0 < w.orderWindow ∧ w.tailControlled ∧
    w.momentBudget ≤ w.orderWindow + w.momentWindow + w.tailWindow + w.slack

def MomentTauberianRefinementWindow.certificate
    (w : MomentTauberianRefinementWindow) : ℕ :=
  w.orderWindow + w.momentWindow + w.tailWindow + w.momentBudget + w.slack

theorem momentTauberianRefinement_budget_le_certificate
    (w : MomentTauberianRefinementWindow) :
    w.momentBudget ≤ w.certificate := by
  unfold MomentTauberianRefinementWindow.certificate
  omega

def sampleMomentTauberianRefinementWindow :
    MomentTauberianRefinementWindow :=
  { orderWindow := 3, momentWindow := 8, tailWindow := 2,
    momentBudget := 14, slack := 1 }

example : momentTauberianRefinementWindowReady
    sampleMomentTauberianRefinementWindow := by
  norm_num [momentTauberianRefinementWindowReady,
    MomentTauberianRefinementWindow.tailControlled, sampleMomentTauberianRefinementWindow]


structure MomentTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MomentTauberianSchemasBudgetCertificate.controlled
    (c : MomentTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MomentTauberianSchemasBudgetCertificate.budgetControlled
    (c : MomentTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MomentTauberianSchemasBudgetCertificate.Ready
    (c : MomentTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MomentTauberianSchemasBudgetCertificate.size
    (c : MomentTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem momentTauberianSchemas_budgetCertificate_le_size
    (c : MomentTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMomentTauberianSchemasBudgetCertificate :
    MomentTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleMomentTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MomentTauberianSchemasBudgetCertificate.controlled,
      sampleMomentTauberianSchemasBudgetCertificate]
  · norm_num [MomentTauberianSchemasBudgetCertificate.budgetControlled,
      sampleMomentTauberianSchemasBudgetCertificate]

example :
    sampleMomentTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMomentTauberianSchemasBudgetCertificate.size := by
  apply momentTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [MomentTauberianSchemasBudgetCertificate.controlled,
      sampleMomentTauberianSchemasBudgetCertificate]
  · norm_num [MomentTauberianSchemasBudgetCertificate.budgetControlled,
      sampleMomentTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMomentTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MomentTauberianSchemasBudgetCertificate.controlled,
      sampleMomentTauberianSchemasBudgetCertificate]
  · norm_num [MomentTauberianSchemasBudgetCertificate.budgetControlled,
      sampleMomentTauberianSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMomentTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMomentTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MomentTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMomentTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMomentTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.MomentTauberianSchemas
