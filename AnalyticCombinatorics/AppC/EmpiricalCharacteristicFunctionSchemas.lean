import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Empirical characteristic function schemas.

This module records finite bookkeeping for empirical characteristic functions:
a positive sample size controls frequency probes with error slack.
-/

namespace AnalyticCombinatorics.AppC.EmpiricalCharacteristicFunctionSchemas

structure EmpiricalCharacteristicData where
  sampleSize : ℕ
  frequencyProbes : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def hasSampleSize (d : EmpiricalCharacteristicData) : Prop :=
  0 < d.sampleSize

def frequencyProbesControlled (d : EmpiricalCharacteristicData) : Prop :=
  d.frequencyProbes ≤ d.sampleSize + d.errorSlack

def empiricalCharacteristicReady (d : EmpiricalCharacteristicData) : Prop :=
  hasSampleSize d ∧ frequencyProbesControlled d

def empiricalCharacteristicBudget (d : EmpiricalCharacteristicData) : ℕ :=
  d.sampleSize + d.frequencyProbes + d.errorSlack

theorem empiricalCharacteristicReady.hasSampleSize
    {d : EmpiricalCharacteristicData}
    (h : empiricalCharacteristicReady d) :
    hasSampleSize d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem frequencyProbes_le_budget (d : EmpiricalCharacteristicData) :
    d.frequencyProbes ≤ empiricalCharacteristicBudget d := by
  unfold empiricalCharacteristicBudget
  omega

def sampleEmpiricalCharacteristicData : EmpiricalCharacteristicData :=
  { sampleSize := 6, frequencyProbes := 8, errorSlack := 3 }

example : empiricalCharacteristicReady sampleEmpiricalCharacteristicData := by
  norm_num [empiricalCharacteristicReady, hasSampleSize]
  norm_num [frequencyProbesControlled, sampleEmpiricalCharacteristicData]

example : empiricalCharacteristicBudget sampleEmpiricalCharacteristicData = 17 := by
  native_decide

structure EmpiricalCharacteristicWindow where
  sampleWindow : ℕ
  frequencyWindow : ℕ
  errorSlack : ℕ
  characteristicBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EmpiricalCharacteristicWindow.frequencyControlled
    (w : EmpiricalCharacteristicWindow) : Prop :=
  w.frequencyWindow ≤ w.sampleWindow + w.errorSlack + w.slack

def empiricalCharacteristicWindowReady (w : EmpiricalCharacteristicWindow) : Prop :=
  0 < w.sampleWindow ∧ w.frequencyControlled ∧
    w.characteristicBudget ≤ w.sampleWindow + w.frequencyWindow + w.slack

def EmpiricalCharacteristicWindow.certificate (w : EmpiricalCharacteristicWindow) : ℕ :=
  w.sampleWindow + w.frequencyWindow + w.errorSlack + w.characteristicBudget + w.slack

theorem empiricalCharacteristic_characteristicBudget_le_certificate
    (w : EmpiricalCharacteristicWindow) :
    w.characteristicBudget ≤ w.certificate := by
  unfold EmpiricalCharacteristicWindow.certificate
  omega

def sampleEmpiricalCharacteristicWindow : EmpiricalCharacteristicWindow :=
  { sampleWindow := 5, frequencyWindow := 7, errorSlack := 2,
    characteristicBudget := 14, slack := 2 }

example : empiricalCharacteristicWindowReady sampleEmpiricalCharacteristicWindow := by
  norm_num [empiricalCharacteristicWindowReady,
    EmpiricalCharacteristicWindow.frequencyControlled, sampleEmpiricalCharacteristicWindow]


structure EmpiricalCharacteristicFunctionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EmpiricalCharacteristicFunctionSchemasBudgetCertificate.controlled
    (c : EmpiricalCharacteristicFunctionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def EmpiricalCharacteristicFunctionSchemasBudgetCertificate.budgetControlled
    (c : EmpiricalCharacteristicFunctionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def EmpiricalCharacteristicFunctionSchemasBudgetCertificate.Ready
    (c : EmpiricalCharacteristicFunctionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EmpiricalCharacteristicFunctionSchemasBudgetCertificate.size
    (c : EmpiricalCharacteristicFunctionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem empiricalCharacteristicFunctionSchemas_budgetCertificate_le_size
    (c : EmpiricalCharacteristicFunctionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate :
    EmpiricalCharacteristicFunctionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EmpiricalCharacteristicFunctionSchemasBudgetCertificate.controlled,
      sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate]
  · norm_num [EmpiricalCharacteristicFunctionSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate]

example : sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EmpiricalCharacteristicFunctionSchemasBudgetCertificate.controlled,
      sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate]
  · norm_num [EmpiricalCharacteristicFunctionSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate]

example :
    sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate.size := by
  apply empiricalCharacteristicFunctionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [EmpiricalCharacteristicFunctionSchemasBudgetCertificate.controlled,
      sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate]
  · norm_num [EmpiricalCharacteristicFunctionSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List EmpiricalCharacteristicFunctionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleEmpiricalCharacteristicFunctionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.EmpiricalCharacteristicFunctionSchemas
