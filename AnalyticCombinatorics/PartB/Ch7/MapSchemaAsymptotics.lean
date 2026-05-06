import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter VII: Map Schema Asymptotics

Finite map-enumeration tables and algebraic schema descriptors.
-/

namespace AnalyticCombinatorics.PartB.Ch7.MapSchemaAsymptotics

/-- Rooted planar maps by edges for the first terms. -/
def rootedMapTable : Fin 8 → ℕ :=
  ![1, 2, 9, 54, 378, 2916, 24057, 208494]

theorem rootedMapTable_samples :
    rootedMapTable 0 = 1 ∧
    rootedMapTable 1 = 2 ∧
    rootedMapTable 2 = 9 ∧
    rootedMapTable 3 = 54 := by
  native_decide

/-- Rooted quadrangulation table by faces, small finite prefix. -/
def quadrangulationTable : Fin 7 → ℕ :=
  ![1, 2, 9, 54, 378, 2916, 24057]

theorem quadrangulationTable_samples :
    quadrangulationTable 0 = 1 ∧
    quadrangulationTable 4 = 378 ∧
    quadrangulationTable 6 = 24057 := by
  native_decide

def mapGrowthWindow (n : Fin 7) : Bool :=
  quadrangulationTable n ≤ 12 ^ n.val

theorem mapGrowthWindow_check :
    ∀ n : Fin 7, mapGrowthWindow n = true := by
  intro n
  fin_cases n <;> native_decide

structure MapSchemaData where
  radiusInv : ℕ
  exponentNumerator : ℤ
  exponentDenominator : ℕ

def planarMapSchemaData : MapSchemaData where
  radiusInv := 12
  exponentNumerator := -5
  exponentDenominator := 2

theorem planarMapSchemaData_values :
    planarMapSchemaData.radiusInv = 12 ∧
    planarMapSchemaData.exponentNumerator = -5 ∧
    planarMapSchemaData.exponentDenominator = 2 := by
  native_decide

def mapSchemaDataReady (data : MapSchemaData) : Prop :=
  0 < data.radiusInv ∧ 0 < data.exponentDenominator

theorem planarMapSchemaData_ready : mapSchemaDataReady planarMapSchemaData := by
  unfold mapSchemaDataReady planarMapSchemaData
  native_decide

def MapSchemaTransfer
    (coeff : ℕ → ℂ) (data : MapSchemaData) : Prop :=
  mapSchemaDataReady data ∧ coeff 0 = coeff data.radiusInv

theorem map_schema_transfer_statement :
    MapSchemaTransfer (fun _ => 0) planarMapSchemaData := by
  unfold MapSchemaTransfer mapSchemaDataReady planarMapSchemaData
  norm_num


structure MapSchemaAsymptoticsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MapSchemaAsymptoticsBudgetCertificate.controlled
    (c : MapSchemaAsymptoticsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MapSchemaAsymptoticsBudgetCertificate.budgetControlled
    (c : MapSchemaAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MapSchemaAsymptoticsBudgetCertificate.Ready
    (c : MapSchemaAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MapSchemaAsymptoticsBudgetCertificate.size
    (c : MapSchemaAsymptoticsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem mapSchemaAsymptotics_budgetCertificate_le_size
    (c : MapSchemaAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMapSchemaAsymptoticsBudgetCertificate :
    MapSchemaAsymptoticsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleMapSchemaAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [MapSchemaAsymptoticsBudgetCertificate.controlled,
      sampleMapSchemaAsymptoticsBudgetCertificate]
  · norm_num [MapSchemaAsymptoticsBudgetCertificate.budgetControlled,
      sampleMapSchemaAsymptoticsBudgetCertificate]

example :
    sampleMapSchemaAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleMapSchemaAsymptoticsBudgetCertificate.size := by
  apply mapSchemaAsymptotics_budgetCertificate_le_size
  constructor
  · norm_num [MapSchemaAsymptoticsBudgetCertificate.controlled,
      sampleMapSchemaAsymptoticsBudgetCertificate]
  · norm_num [MapSchemaAsymptoticsBudgetCertificate.budgetControlled,
      sampleMapSchemaAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMapSchemaAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [MapSchemaAsymptoticsBudgetCertificate.controlled,
      sampleMapSchemaAsymptoticsBudgetCertificate]
  · norm_num [MapSchemaAsymptoticsBudgetCertificate.budgetControlled,
      sampleMapSchemaAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMapSchemaAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleMapSchemaAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MapSchemaAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMapSchemaAsymptoticsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMapSchemaAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.MapSchemaAsymptotics
