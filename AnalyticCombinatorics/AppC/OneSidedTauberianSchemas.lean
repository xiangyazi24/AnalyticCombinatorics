import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
One-sided Tauberian schema bookkeeping.

The hypotheses record a lower envelope, an upper envelope, and positivity of
the normalizing scale.
-/

namespace AnalyticCombinatorics.AppC.OneSidedTauberianSchemas

structure OneSidedTauberianData where
  lowerEnvelope : ℕ
  upperEnvelope : ℕ
  scale : ℕ
deriving DecidableEq, Repr

def envelopeOrdered (d : OneSidedTauberianData) : Prop :=
  d.lowerEnvelope ≤ d.upperEnvelope

def positiveScale (d : OneSidedTauberianData) : Prop :=
  0 < d.scale

def oneSidedReady (d : OneSidedTauberianData) : Prop :=
  envelopeOrdered d ∧ positiveScale d

def envelopeWidth (d : OneSidedTauberianData) : ℕ :=
  d.upperEnvelope - d.lowerEnvelope

theorem oneSidedReady.ordered {d : OneSidedTauberianData}
    (h : oneSidedReady d) :
    envelopeOrdered d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem envelopeWidth_add {d : OneSidedTauberianData}
    (h : envelopeOrdered d) :
    envelopeWidth d + d.lowerEnvelope = d.upperEnvelope := by
  unfold envelopeWidth envelopeOrdered at *
  omega

def sampleOneSided : OneSidedTauberianData :=
  { lowerEnvelope := 5, upperEnvelope := 12, scale := 3 }

example : oneSidedReady sampleOneSided := by
  norm_num [oneSidedReady, envelopeOrdered, positiveScale, sampleOneSided]

example : envelopeWidth sampleOneSided = 7 := by
  native_decide

structure OneSidedTauberianWindow where
  lowerEnvelope : ℕ
  upperEnvelope : ℕ
  scale : ℕ
  remainderBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def OneSidedTauberianWindow.envelopeControlled (w : OneSidedTauberianWindow) : Prop :=
  w.lowerEnvelope ≤ w.upperEnvelope + w.slack

def OneSidedTauberianWindow.remainderControlled (w : OneSidedTauberianWindow) : Prop :=
  w.remainderBudget ≤ w.lowerEnvelope + w.upperEnvelope + w.scale + w.slack

def oneSidedTauberianWindowReady (w : OneSidedTauberianWindow) : Prop :=
  0 < w.scale ∧
    w.envelopeControlled ∧
    w.remainderControlled

def OneSidedTauberianWindow.certificate (w : OneSidedTauberianWindow) : ℕ :=
  w.lowerEnvelope + w.upperEnvelope + w.scale + w.slack

theorem oneSided_remainderBudget_le_certificate {w : OneSidedTauberianWindow}
    (h : oneSidedTauberianWindowReady w) :
    w.remainderBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hremainder⟩
  exact hremainder

def sampleOneSidedTauberianWindow : OneSidedTauberianWindow :=
  { lowerEnvelope := 5, upperEnvelope := 12, scale := 3, remainderBudget := 19, slack := 0 }

example : oneSidedTauberianWindowReady sampleOneSidedTauberianWindow := by
  norm_num [oneSidedTauberianWindowReady, OneSidedTauberianWindow.envelopeControlled,
    OneSidedTauberianWindow.remainderControlled, sampleOneSidedTauberianWindow]

example : sampleOneSidedTauberianWindow.certificate = 20 := by
  native_decide


structure OneSidedTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def OneSidedTauberianSchemasBudgetCertificate.controlled
    (c : OneSidedTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def OneSidedTauberianSchemasBudgetCertificate.budgetControlled
    (c : OneSidedTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def OneSidedTauberianSchemasBudgetCertificate.Ready
    (c : OneSidedTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def OneSidedTauberianSchemasBudgetCertificate.size
    (c : OneSidedTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem oneSidedTauberianSchemas_budgetCertificate_le_size
    (c : OneSidedTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleOneSidedTauberianSchemasBudgetCertificate :
    OneSidedTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleOneSidedTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [OneSidedTauberianSchemasBudgetCertificate.controlled,
      sampleOneSidedTauberianSchemasBudgetCertificate]
  · norm_num [OneSidedTauberianSchemasBudgetCertificate.budgetControlled,
      sampleOneSidedTauberianSchemasBudgetCertificate]

example : sampleOneSidedTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [OneSidedTauberianSchemasBudgetCertificate.controlled,
      sampleOneSidedTauberianSchemasBudgetCertificate]
  · norm_num [OneSidedTauberianSchemasBudgetCertificate.budgetControlled,
      sampleOneSidedTauberianSchemasBudgetCertificate]

example :
    sampleOneSidedTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleOneSidedTauberianSchemasBudgetCertificate.size := by
  apply oneSidedTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [OneSidedTauberianSchemasBudgetCertificate.controlled,
      sampleOneSidedTauberianSchemasBudgetCertificate]
  · norm_num [OneSidedTauberianSchemasBudgetCertificate.budgetControlled,
      sampleOneSidedTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleOneSidedTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleOneSidedTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List OneSidedTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleOneSidedTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleOneSidedTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.OneSidedTauberianSchemas
