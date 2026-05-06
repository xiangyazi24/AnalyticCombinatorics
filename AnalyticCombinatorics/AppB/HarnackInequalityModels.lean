import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Harnack-inequality bookkeeping models.

The analytic inequality is represented by finite lower and upper budgets
for positive harmonic functions.
-/

namespace AnalyticCombinatorics.AppB.HarnackInequalityModels

structure HarnackDatum where
  lowerValue : ℕ
  upperValue : ℕ
  constantBudget : ℕ
deriving DecidableEq, Repr

def positiveLowerValue (d : HarnackDatum) : Prop :=
  0 < d.lowerValue

def harnackBounded (d : HarnackDatum) : Prop :=
  d.upperValue ≤ d.constantBudget * d.lowerValue

def harnackReady (d : HarnackDatum) : Prop :=
  positiveLowerValue d ∧ harnackBounded d

def harnackSlack (d : HarnackDatum) : ℕ :=
  d.constantBudget * d.lowerValue - d.upperValue

theorem harnackReady.bound {d : HarnackDatum}
    (h : harnackReady d) :
    positiveLowerValue d ∧ harnackBounded d := by
  refine ⟨h.1, h.2⟩

theorem harnackSlack_add {d : HarnackDatum}
    (h : harnackBounded d) :
    harnackSlack d + d.upperValue = d.constantBudget * d.lowerValue := by
  unfold harnackSlack harnackBounded at *
  omega

def sampleHarnack : HarnackDatum :=
  { lowerValue := 3, upperValue := 10, constantBudget := 4 }

example : harnackReady sampleHarnack := by
  norm_num [harnackReady, positiveLowerValue, harnackBounded, sampleHarnack]

example : harnackSlack sampleHarnack = 2 := by
  native_decide

structure HarnackWindow where
  lowerValue : ℕ
  upperValue : ℕ
  constantBudget : ℕ
  domainSlack : ℕ
deriving DecidableEq, Repr

def HarnackWindow.lowerReady (w : HarnackWindow) : Prop :=
  0 < w.lowerValue

def HarnackWindow.boundControlled (w : HarnackWindow) : Prop :=
  w.upperValue ≤ w.constantBudget * w.lowerValue + w.domainSlack

def HarnackWindow.ready (w : HarnackWindow) : Prop :=
  w.lowerReady ∧ w.boundControlled

def HarnackWindow.certificate (w : HarnackWindow) : ℕ :=
  w.lowerValue + w.upperValue + w.constantBudget + w.domainSlack

theorem upperValue_le_certificate (w : HarnackWindow) :
    w.upperValue ≤ w.certificate := by
  unfold HarnackWindow.certificate
  omega

def sampleHarnackWindow : HarnackWindow :=
  { lowerValue := 3, upperValue := 10, constantBudget := 4, domainSlack := 0 }

example : sampleHarnackWindow.ready := by
  norm_num [sampleHarnackWindow, HarnackWindow.ready,
    HarnackWindow.lowerReady, HarnackWindow.boundControlled]


structure HarnackInequalityModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HarnackInequalityModelsBudgetCertificate.controlled
    (c : HarnackInequalityModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HarnackInequalityModelsBudgetCertificate.budgetControlled
    (c : HarnackInequalityModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HarnackInequalityModelsBudgetCertificate.Ready
    (c : HarnackInequalityModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HarnackInequalityModelsBudgetCertificate.size
    (c : HarnackInequalityModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem harnackInequalityModels_budgetCertificate_le_size
    (c : HarnackInequalityModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHarnackInequalityModelsBudgetCertificate :
    HarnackInequalityModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleHarnackInequalityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [HarnackInequalityModelsBudgetCertificate.controlled,
      sampleHarnackInequalityModelsBudgetCertificate]
  · norm_num [HarnackInequalityModelsBudgetCertificate.budgetControlled,
      sampleHarnackInequalityModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHarnackInequalityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleHarnackInequalityModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleHarnackInequalityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [HarnackInequalityModelsBudgetCertificate.controlled,
      sampleHarnackInequalityModelsBudgetCertificate]
  · norm_num [HarnackInequalityModelsBudgetCertificate.budgetControlled,
      sampleHarnackInequalityModelsBudgetCertificate]

example :
    sampleHarnackInequalityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleHarnackInequalityModelsBudgetCertificate.size := by
  apply harnackInequalityModels_budgetCertificate_le_size
  constructor
  · norm_num [HarnackInequalityModelsBudgetCertificate.controlled,
      sampleHarnackInequalityModelsBudgetCertificate]
  · norm_num [HarnackInequalityModelsBudgetCertificate.budgetControlled,
      sampleHarnackInequalityModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List HarnackInequalityModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHarnackInequalityModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHarnackInequalityModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.HarnackInequalityModels
