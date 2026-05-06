import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Delta-domain transfer schemas.

The finite schema records aperture scale, radial margin, and error slack.
-/

namespace AnalyticCombinatorics.PartB.Ch6.DeltaDomainTransferSchemas

structure DeltaDomainTransferData where
  apertureScale : ℕ
  radialMargin : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def apertureScalePositive (d : DeltaDomainTransferData) : Prop :=
  0 < d.apertureScale

def radialMarginControlled (d : DeltaDomainTransferData) : Prop :=
  d.radialMargin ≤ d.apertureScale + d.errorSlack

def deltaDomainTransferReady (d : DeltaDomainTransferData) : Prop :=
  apertureScalePositive d ∧ radialMarginControlled d

def deltaDomainTransferBudget (d : DeltaDomainTransferData) : ℕ :=
  d.apertureScale + d.radialMargin + d.errorSlack

theorem deltaDomainTransferReady.aperture {d : DeltaDomainTransferData}
    (h : deltaDomainTransferReady d) :
    apertureScalePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem radialMargin_le_deltaDomainBudget (d : DeltaDomainTransferData) :
    d.radialMargin ≤ deltaDomainTransferBudget d := by
  unfold deltaDomainTransferBudget
  omega

def sampleDeltaDomainTransferData : DeltaDomainTransferData :=
  { apertureScale := 5, radialMargin := 7, errorSlack := 3 }

example : deltaDomainTransferReady sampleDeltaDomainTransferData := by
  norm_num [deltaDomainTransferReady, apertureScalePositive]
  norm_num [radialMarginControlled, sampleDeltaDomainTransferData]

example : deltaDomainTransferBudget sampleDeltaDomainTransferData = 15 := by
  native_decide

structure DeltaTransferWindow where
  apertureScale : ℕ
  radialMargin : ℕ
  transferError : ℕ
  coefficientWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DeltaTransferWindow.radialControlled (w : DeltaTransferWindow) : Prop :=
  w.radialMargin ≤ w.apertureScale + w.transferError + w.slack

def DeltaTransferWindow.coefficientControlled (w : DeltaTransferWindow) : Prop :=
  w.coefficientWindow ≤ w.apertureScale + w.radialMargin + w.transferError + w.slack

def deltaTransferWindowReady (w : DeltaTransferWindow) : Prop :=
  0 < w.apertureScale ∧
    w.radialControlled ∧
    w.coefficientControlled

def DeltaTransferWindow.certificate (w : DeltaTransferWindow) : ℕ :=
  w.apertureScale + w.radialMargin + w.transferError + w.slack

theorem delta_coefficientWindow_le_certificate {w : DeltaTransferWindow}
    (h : deltaTransferWindowReady w) :
    w.coefficientWindow ≤ w.certificate := by
  rcases h with ⟨_, _, hcoeff⟩
  exact hcoeff

def sampleDeltaTransferWindow : DeltaTransferWindow :=
  { apertureScale := 5, radialMargin := 7, transferError := 3, coefficientWindow := 10,
    slack := 0 }

example : deltaTransferWindowReady sampleDeltaTransferWindow := by
  norm_num [deltaTransferWindowReady, DeltaTransferWindow.radialControlled,
    DeltaTransferWindow.coefficientControlled, sampleDeltaTransferWindow]

example : sampleDeltaTransferWindow.certificate = 15 := by
  native_decide


structure DeltaDomainTransferSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DeltaDomainTransferSchemasBudgetCertificate.controlled
    (c : DeltaDomainTransferSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DeltaDomainTransferSchemasBudgetCertificate.budgetControlled
    (c : DeltaDomainTransferSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DeltaDomainTransferSchemasBudgetCertificate.Ready
    (c : DeltaDomainTransferSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DeltaDomainTransferSchemasBudgetCertificate.size
    (c : DeltaDomainTransferSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem deltaDomainTransferSchemas_budgetCertificate_le_size
    (c : DeltaDomainTransferSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDeltaDomainTransferSchemasBudgetCertificate :
    DeltaDomainTransferSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDeltaDomainTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DeltaDomainTransferSchemasBudgetCertificate.controlled,
      sampleDeltaDomainTransferSchemasBudgetCertificate]
  · norm_num [DeltaDomainTransferSchemasBudgetCertificate.budgetControlled,
      sampleDeltaDomainTransferSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDeltaDomainTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDeltaDomainTransferSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDeltaDomainTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DeltaDomainTransferSchemasBudgetCertificate.controlled,
      sampleDeltaDomainTransferSchemasBudgetCertificate]
  · norm_num [DeltaDomainTransferSchemasBudgetCertificate.budgetControlled,
      sampleDeltaDomainTransferSchemasBudgetCertificate]

example :
    sampleDeltaDomainTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDeltaDomainTransferSchemasBudgetCertificate.size := by
  apply deltaDomainTransferSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DeltaDomainTransferSchemasBudgetCertificate.controlled,
      sampleDeltaDomainTransferSchemasBudgetCertificate]
  · norm_num [DeltaDomainTransferSchemasBudgetCertificate.budgetControlled,
      sampleDeltaDomainTransferSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List DeltaDomainTransferSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDeltaDomainTransferSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDeltaDomainTransferSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.DeltaDomainTransferSchemas
