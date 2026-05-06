import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Exponential formula bookkeeping.
-/

namespace AnalyticCombinatorics.PartA.Ch2.ExponentialFormula

structure ExponentialFormulaData where
  componentCount : ℕ
  assemblySize : ℕ
  componentSlack : ℕ
deriving DecidableEq, Repr

def exponentialFormulaReady (d : ExponentialFormulaData) : Prop :=
  0 < d.componentCount ∧ d.assemblySize ≤ d.componentCount + d.componentSlack

def exponentialFormulaBudget (d : ExponentialFormulaData) : ℕ :=
  d.componentCount + d.assemblySize + d.componentSlack

theorem assemblySize_le_budget (d : ExponentialFormulaData) :
    d.assemblySize ≤ exponentialFormulaBudget d := by
  unfold exponentialFormulaBudget
  omega

def sampleExponentialFormulaData : ExponentialFormulaData :=
  { componentCount := 7, assemblySize := 9, componentSlack := 3 }

example : exponentialFormulaReady sampleExponentialFormulaData := by
  norm_num [exponentialFormulaReady, sampleExponentialFormulaData]

example : exponentialFormulaBudget sampleExponentialFormulaData = 19 := by native_decide

structure ComponentInventory where
  labels : ℕ
  componentTypes : ℕ
  selectedComponents : ℕ
  assemblySlack : ℕ
deriving DecidableEq, Repr

def ComponentInventory.labelledSlots (i : ComponentInventory) : ℕ :=
  i.labels + i.assemblySlack

def ComponentInventory.ready (i : ComponentInventory) : Prop :=
  0 < i.componentTypes ∧ i.selectedComponents ≤ i.labelledSlots

def ComponentInventory.exponentialWeight (i : ComponentInventory) : ℕ :=
  i.componentTypes.factorial * (i.selectedComponents + 1)

def ComponentInventory.certificate (i : ComponentInventory) : ℕ :=
  i.labels + i.componentTypes + i.selectedComponents + i.assemblySlack

theorem selectedComponents_le_certificate (i : ComponentInventory) :
    i.selectedComponents ≤ i.certificate := by
  unfold ComponentInventory.certificate
  omega

def sampleComponentInventory : ComponentInventory :=
  { labels := 6, componentTypes := 3, selectedComponents := 5, assemblySlack := 0 }

example : sampleComponentInventory.ready := by
  norm_num [sampleComponentInventory, ComponentInventory.ready, ComponentInventory.labelledSlots]

example : sampleComponentInventory.exponentialWeight = 36 := by
  norm_num [sampleComponentInventory, ComponentInventory.exponentialWeight]


structure ExponentialFormulaBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExponentialFormulaBudgetCertificate.controlled
    (c : ExponentialFormulaBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ExponentialFormulaBudgetCertificate.budgetControlled
    (c : ExponentialFormulaBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ExponentialFormulaBudgetCertificate.Ready
    (c : ExponentialFormulaBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ExponentialFormulaBudgetCertificate.size
    (c : ExponentialFormulaBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem exponentialFormula_budgetCertificate_le_size
    (c : ExponentialFormulaBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleExponentialFormulaBudgetCertificate :
    ExponentialFormulaBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleExponentialFormulaBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialFormulaBudgetCertificate.controlled,
      sampleExponentialFormulaBudgetCertificate]
  · norm_num [ExponentialFormulaBudgetCertificate.budgetControlled,
      sampleExponentialFormulaBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleExponentialFormulaBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialFormulaBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleExponentialFormulaBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialFormulaBudgetCertificate.controlled,
      sampleExponentialFormulaBudgetCertificate]
  · norm_num [ExponentialFormulaBudgetCertificate.budgetControlled,
      sampleExponentialFormulaBudgetCertificate]

example :
    sampleExponentialFormulaBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialFormulaBudgetCertificate.size := by
  apply exponentialFormula_budgetCertificate_le_size
  constructor
  · norm_num [ExponentialFormulaBudgetCertificate.controlled,
      sampleExponentialFormulaBudgetCertificate]
  · norm_num [ExponentialFormulaBudgetCertificate.budgetControlled,
      sampleExponentialFormulaBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ExponentialFormulaBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleExponentialFormulaBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleExponentialFormulaBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.ExponentialFormula
