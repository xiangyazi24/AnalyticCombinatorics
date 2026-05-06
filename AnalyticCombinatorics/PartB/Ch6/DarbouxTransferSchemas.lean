import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Darboux transfer schemas.

The finite record stores boundary order, local expansion budget, and
coefficient slack.
-/

namespace AnalyticCombinatorics.PartB.Ch6.DarbouxTransferSchemas

structure DarbouxTransferData where
  boundaryOrder : ℕ
  localExpansionBudget : ℕ
  coefficientSlack : ℕ
deriving DecidableEq, Repr

def boundaryOrderPositive (d : DarbouxTransferData) : Prop :=
  0 < d.boundaryOrder

def expansionControlled (d : DarbouxTransferData) : Prop :=
  d.localExpansionBudget ≤ d.boundaryOrder + d.coefficientSlack

def darbouxTransferReady (d : DarbouxTransferData) : Prop :=
  boundaryOrderPositive d ∧ expansionControlled d

def darbouxTransferBudget (d : DarbouxTransferData) : ℕ :=
  d.boundaryOrder + d.localExpansionBudget + d.coefficientSlack

theorem darbouxTransferReady.boundary {d : DarbouxTransferData}
    (h : darbouxTransferReady d) :
    boundaryOrderPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem localExpansion_le_darbouxBudget (d : DarbouxTransferData) :
    d.localExpansionBudget ≤ darbouxTransferBudget d := by
  unfold darbouxTransferBudget
  omega

def sampleDarbouxTransferData : DarbouxTransferData :=
  { boundaryOrder := 4, localExpansionBudget := 6, coefficientSlack := 3 }

example : darbouxTransferReady sampleDarbouxTransferData := by
  norm_num [darbouxTransferReady, boundaryOrderPositive]
  norm_num [expansionControlled, sampleDarbouxTransferData]

example : darbouxTransferBudget sampleDarbouxTransferData = 13 := by
  native_decide

structure DarbouxTransferWindow where
  boundaryOrder : ℕ
  localExpansionBudget : ℕ
  coefficientSlack : ℕ
  coefficientBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DarbouxTransferWindow.expansionControlled (w : DarbouxTransferWindow) : Prop :=
  w.localExpansionBudget ≤ w.boundaryOrder + w.coefficientSlack + w.slack

def DarbouxTransferWindow.coefficientControlled (w : DarbouxTransferWindow) : Prop :=
  w.coefficientBudget ≤ w.boundaryOrder + w.localExpansionBudget + w.coefficientSlack + w.slack

def darbouxTransferWindowReady (w : DarbouxTransferWindow) : Prop :=
  0 < w.boundaryOrder ∧
    w.expansionControlled ∧
    w.coefficientControlled

def DarbouxTransferWindow.certificate (w : DarbouxTransferWindow) : ℕ :=
  w.boundaryOrder + w.localExpansionBudget + w.coefficientSlack + w.slack

theorem darbouxTransfer_coefficientBudget_le_certificate {w : DarbouxTransferWindow}
    (h : darbouxTransferWindowReady w) :
    w.coefficientBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hcoeff⟩
  exact hcoeff

def sampleDarbouxTransferWindow : DarbouxTransferWindow :=
  { boundaryOrder := 4, localExpansionBudget := 6, coefficientSlack := 3, coefficientBudget := 12,
    slack := 0 }

example : darbouxTransferWindowReady sampleDarbouxTransferWindow := by
  norm_num [darbouxTransferWindowReady, DarbouxTransferWindow.expansionControlled,
    DarbouxTransferWindow.coefficientControlled, sampleDarbouxTransferWindow]

example : sampleDarbouxTransferWindow.certificate = 13 := by
  native_decide


structure DarbouxTransferSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DarbouxTransferSchemasBudgetCertificate.controlled
    (c : DarbouxTransferSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DarbouxTransferSchemasBudgetCertificate.budgetControlled
    (c : DarbouxTransferSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DarbouxTransferSchemasBudgetCertificate.Ready
    (c : DarbouxTransferSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DarbouxTransferSchemasBudgetCertificate.size
    (c : DarbouxTransferSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem darbouxTransferSchemas_budgetCertificate_le_size
    (c : DarbouxTransferSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDarbouxTransferSchemasBudgetCertificate :
    DarbouxTransferSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDarbouxTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DarbouxTransferSchemasBudgetCertificate.controlled,
      sampleDarbouxTransferSchemasBudgetCertificate]
  · norm_num [DarbouxTransferSchemasBudgetCertificate.budgetControlled,
      sampleDarbouxTransferSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDarbouxTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDarbouxTransferSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDarbouxTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DarbouxTransferSchemasBudgetCertificate.controlled,
      sampleDarbouxTransferSchemasBudgetCertificate]
  · norm_num [DarbouxTransferSchemasBudgetCertificate.budgetControlled,
      sampleDarbouxTransferSchemasBudgetCertificate]

example :
    sampleDarbouxTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDarbouxTransferSchemasBudgetCertificate.size := by
  apply darbouxTransferSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DarbouxTransferSchemasBudgetCertificate.controlled,
      sampleDarbouxTransferSchemasBudgetCertificate]
  · norm_num [DarbouxTransferSchemasBudgetCertificate.budgetControlled,
      sampleDarbouxTransferSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List DarbouxTransferSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDarbouxTransferSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDarbouxTransferSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.DarbouxTransferSchemas
