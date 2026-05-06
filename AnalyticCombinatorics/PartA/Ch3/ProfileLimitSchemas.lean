import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Profile limit schemas.

The finite record tracks profile width, sample budget, and deviation
budget for parameter profiles.
-/

namespace AnalyticCombinatorics.PartA.Ch3.ProfileLimitSchemas

structure ProfileLimitData where
  profileWidth : ℕ
  sampleBudget : ℕ
  deviationBudget : ℕ
deriving DecidableEq, Repr

def profileWidthPositive (d : ProfileLimitData) : Prop :=
  0 < d.profileWidth

def deviationControlled (d : ProfileLimitData) : Prop :=
  d.deviationBudget ≤ d.profileWidth + d.sampleBudget

def profileLimitReady (d : ProfileLimitData) : Prop :=
  profileWidthPositive d ∧ deviationControlled d

def profileLimitBudget (d : ProfileLimitData) : ℕ :=
  d.profileWidth + d.sampleBudget + d.deviationBudget

theorem profileLimitReady.width {d : ProfileLimitData}
    (h : profileLimitReady d) :
    profileWidthPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem sampleBudget_le_profileBudget (d : ProfileLimitData) :
    d.sampleBudget ≤ profileLimitBudget d := by
  unfold profileLimitBudget
  omega

def sampleProfileLimitData : ProfileLimitData :=
  { profileWidth := 4, sampleBudget := 9, deviationBudget := 10 }

example : profileLimitReady sampleProfileLimitData := by
  norm_num [profileLimitReady, profileWidthPositive]
  norm_num [deviationControlled, sampleProfileLimitData]

example : profileLimitBudget sampleProfileLimitData = 23 := by
  native_decide

structure ProfileLimitWindow where
  profileWidth : ℕ
  sampleBudget : ℕ
  deviationBudget : ℕ
  envelopeBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProfileLimitWindow.deviationControlled (w : ProfileLimitWindow) : Prop :=
  w.deviationBudget ≤ w.profileWidth + w.sampleBudget + w.slack

def ProfileLimitWindow.envelopeControlled (w : ProfileLimitWindow) : Prop :=
  w.envelopeBudget ≤ w.profileWidth + w.sampleBudget + w.deviationBudget + w.slack

def profileLimitWindowReady (w : ProfileLimitWindow) : Prop :=
  0 < w.profileWidth ∧
    w.deviationControlled ∧
    w.envelopeControlled

def ProfileLimitWindow.certificate (w : ProfileLimitWindow) : ℕ :=
  w.profileWidth + w.sampleBudget + w.deviationBudget + w.slack

theorem profileLimit_envelopeBudget_le_certificate {w : ProfileLimitWindow}
    (h : profileLimitWindowReady w) :
    w.envelopeBudget ≤ w.certificate := by
  rcases h with ⟨_, _, henvelope⟩
  exact henvelope

def sampleProfileLimitWindow : ProfileLimitWindow :=
  { profileWidth := 4, sampleBudget := 9, deviationBudget := 10, envelopeBudget := 22,
    slack := 0 }

example : profileLimitWindowReady sampleProfileLimitWindow := by
  norm_num [profileLimitWindowReady, ProfileLimitWindow.deviationControlled,
    ProfileLimitWindow.envelopeControlled, sampleProfileLimitWindow]

example : sampleProfileLimitWindow.certificate = 23 := by
  native_decide


structure ProfileLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProfileLimitSchemasBudgetCertificate.controlled
    (c : ProfileLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ProfileLimitSchemasBudgetCertificate.budgetControlled
    (c : ProfileLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ProfileLimitSchemasBudgetCertificate.Ready
    (c : ProfileLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ProfileLimitSchemasBudgetCertificate.size
    (c : ProfileLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem profileLimitSchemas_budgetCertificate_le_size
    (c : ProfileLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleProfileLimitSchemasBudgetCertificate :
    ProfileLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleProfileLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ProfileLimitSchemasBudgetCertificate.controlled,
      sampleProfileLimitSchemasBudgetCertificate]
  · norm_num [ProfileLimitSchemasBudgetCertificate.budgetControlled,
      sampleProfileLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleProfileLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleProfileLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleProfileLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ProfileLimitSchemasBudgetCertificate.controlled,
      sampleProfileLimitSchemasBudgetCertificate]
  · norm_num [ProfileLimitSchemasBudgetCertificate.budgetControlled,
      sampleProfileLimitSchemasBudgetCertificate]

example :
    sampleProfileLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleProfileLimitSchemasBudgetCertificate.size := by
  apply profileLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ProfileLimitSchemasBudgetCertificate.controlled,
      sampleProfileLimitSchemasBudgetCertificate]
  · norm_num [ProfileLimitSchemasBudgetCertificate.budgetControlled,
      sampleProfileLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ProfileLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleProfileLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleProfileLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.ProfileLimitSchemas
