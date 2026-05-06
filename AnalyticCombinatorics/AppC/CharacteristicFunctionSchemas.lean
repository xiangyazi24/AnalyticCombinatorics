import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Characteristic function schemas.

The finite record tracks frequency samples, modulus budget, and tail
budget for characteristic-function arguments.
-/

namespace AnalyticCombinatorics.AppC.CharacteristicFunctionSchemas

structure CharacteristicFunctionData where
  frequencySamples : ℕ
  modulusBudget : ℕ
  tailBudget : ℕ
deriving DecidableEq, Repr

def frequenciesNonempty (d : CharacteristicFunctionData) : Prop :=
  0 < d.frequencySamples

def modulusControlled (d : CharacteristicFunctionData) : Prop :=
  d.modulusBudget ≤ d.frequencySamples + d.tailBudget

def characteristicFunctionReady (d : CharacteristicFunctionData) : Prop :=
  frequenciesNonempty d ∧ modulusControlled d

def characteristicFunctionBudget (d : CharacteristicFunctionData) : ℕ :=
  d.frequencySamples + d.modulusBudget + d.tailBudget

theorem characteristicFunctionReady.frequencies
    {d : CharacteristicFunctionData}
    (h : characteristicFunctionReady d) :
    frequenciesNonempty d ∧ modulusControlled d ∧
      d.modulusBudget ≤ characteristicFunctionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold characteristicFunctionBudget
  omega

theorem modulusBudget_le_characteristicBudget
    (d : CharacteristicFunctionData) :
    d.modulusBudget ≤ characteristicFunctionBudget d := by
  unfold characteristicFunctionBudget
  omega

def sampleCharacteristicFunctionData : CharacteristicFunctionData :=
  { frequencySamples := 7, modulusBudget := 9, tailBudget := 3 }

example : characteristicFunctionReady sampleCharacteristicFunctionData := by
  norm_num [characteristicFunctionReady, frequenciesNonempty]
  norm_num [modulusControlled, sampleCharacteristicFunctionData]

example : characteristicFunctionBudget sampleCharacteristicFunctionData = 19 := by
  native_decide

structure CharacteristicFunctionWindow where
  frequencyWindow : ℕ
  modulusWindow : ℕ
  tailWindow : ℕ
  characteristicBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CharacteristicFunctionWindow.modulusControlled
    (w : CharacteristicFunctionWindow) : Prop :=
  w.modulusWindow ≤ w.frequencyWindow + w.tailWindow + w.slack

def characteristicFunctionWindowReady (w : CharacteristicFunctionWindow) : Prop :=
  0 < w.frequencyWindow ∧ w.modulusControlled ∧
    w.characteristicBudget ≤ w.frequencyWindow + w.modulusWindow + w.tailWindow + w.slack

def CharacteristicFunctionWindow.certificate (w : CharacteristicFunctionWindow) : ℕ :=
  w.frequencyWindow + w.modulusWindow + w.tailWindow + w.characteristicBudget + w.slack

theorem characteristicFunction_budget_le_certificate
    (w : CharacteristicFunctionWindow) :
    w.characteristicBudget ≤ w.certificate := by
  unfold CharacteristicFunctionWindow.certificate
  omega

def sampleCharacteristicFunctionWindow : CharacteristicFunctionWindow :=
  { frequencyWindow := 6, modulusWindow := 8, tailWindow := 2,
    characteristicBudget := 17, slack := 1 }

example : characteristicFunctionWindowReady sampleCharacteristicFunctionWindow := by
  norm_num [characteristicFunctionWindowReady,
    CharacteristicFunctionWindow.modulusControlled, sampleCharacteristicFunctionWindow]


structure CharacteristicFunctionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CharacteristicFunctionSchemasBudgetCertificate.controlled
    (c : CharacteristicFunctionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CharacteristicFunctionSchemasBudgetCertificate.budgetControlled
    (c : CharacteristicFunctionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CharacteristicFunctionSchemasBudgetCertificate.Ready
    (c : CharacteristicFunctionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CharacteristicFunctionSchemasBudgetCertificate.size
    (c : CharacteristicFunctionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem characteristicFunctionSchemas_budgetCertificate_le_size
    (c : CharacteristicFunctionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCharacteristicFunctionSchemasBudgetCertificate :
    CharacteristicFunctionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCharacteristicFunctionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CharacteristicFunctionSchemasBudgetCertificate.controlled,
      sampleCharacteristicFunctionSchemasBudgetCertificate]
  · norm_num [CharacteristicFunctionSchemasBudgetCertificate.budgetControlled,
      sampleCharacteristicFunctionSchemasBudgetCertificate]

example : sampleCharacteristicFunctionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CharacteristicFunctionSchemasBudgetCertificate.controlled,
      sampleCharacteristicFunctionSchemasBudgetCertificate]
  · norm_num [CharacteristicFunctionSchemasBudgetCertificate.budgetControlled,
      sampleCharacteristicFunctionSchemasBudgetCertificate]

example :
    sampleCharacteristicFunctionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCharacteristicFunctionSchemasBudgetCertificate.size := by
  apply characteristicFunctionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CharacteristicFunctionSchemasBudgetCertificate.controlled,
      sampleCharacteristicFunctionSchemasBudgetCertificate]
  · norm_num [CharacteristicFunctionSchemasBudgetCertificate.budgetControlled,
      sampleCharacteristicFunctionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleCharacteristicFunctionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCharacteristicFunctionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CharacteristicFunctionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCharacteristicFunctionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCharacteristicFunctionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.CharacteristicFunctionSchemas
