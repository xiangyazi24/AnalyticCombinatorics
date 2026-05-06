import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random fragmentation process schemas.

The finite schema records fragment count, split budget, and tightness
slack.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomFragmentationProcessSchemas

structure RandomFragmentationProcessData where
  fragmentCount : ℕ
  splitBudget : ℕ
  tightnessSlack : ℕ
deriving DecidableEq, Repr

def fragmentCountPositive (d : RandomFragmentationProcessData) : Prop :=
  0 < d.fragmentCount

def splitBudgetControlled (d : RandomFragmentationProcessData) : Prop :=
  d.splitBudget ≤ d.fragmentCount + d.tightnessSlack

def randomFragmentationProcessReady
    (d : RandomFragmentationProcessData) : Prop :=
  fragmentCountPositive d ∧ splitBudgetControlled d

def randomFragmentationProcessBudget
    (d : RandomFragmentationProcessData) : ℕ :=
  d.fragmentCount + d.splitBudget + d.tightnessSlack

theorem randomFragmentationProcessReady.fragments
    {d : RandomFragmentationProcessData}
    (h : randomFragmentationProcessReady d) :
    fragmentCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem splitBudget_le_fragmentationProcessBudget
    (d : RandomFragmentationProcessData) :
    d.splitBudget ≤ randomFragmentationProcessBudget d := by
  unfold randomFragmentationProcessBudget
  omega

def sampleRandomFragmentationProcessData :
    RandomFragmentationProcessData :=
  { fragmentCount := 7, splitBudget := 9, tightnessSlack := 3 }

example :
    randomFragmentationProcessReady sampleRandomFragmentationProcessData := by
  norm_num [randomFragmentationProcessReady, fragmentCountPositive]
  norm_num [splitBudgetControlled, sampleRandomFragmentationProcessData]

example :
    randomFragmentationProcessBudget
      sampleRandomFragmentationProcessData = 19 := by
  native_decide

/-- Finite executable readiness audit for random fragmentation-process windows. -/
def randomFragmentationProcessListReady
    (windows : List RandomFragmentationProcessData) : Bool :=
  windows.all fun d =>
    0 < d.fragmentCount && d.splitBudget ≤ d.fragmentCount + d.tightnessSlack

theorem randomFragmentationProcessList_readyWindow :
    randomFragmentationProcessListReady
      [{ fragmentCount := 4, splitBudget := 5, tightnessSlack := 1 },
       { fragmentCount := 7, splitBudget := 9, tightnessSlack := 3 }] = true := by
  unfold randomFragmentationProcessListReady
  native_decide

structure RandomFragmentationProcessSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomFragmentationProcessSchemasBudgetCertificate.controlled
    (c : RandomFragmentationProcessSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomFragmentationProcessSchemasBudgetCertificate.budgetControlled
    (c : RandomFragmentationProcessSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomFragmentationProcessSchemasBudgetCertificate.Ready
    (c : RandomFragmentationProcessSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomFragmentationProcessSchemasBudgetCertificate.size
    (c : RandomFragmentationProcessSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomFragmentationProcessSchemas_budgetCertificate_le_size
    (c : RandomFragmentationProcessSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomFragmentationProcessSchemasBudgetCertificate :
    RandomFragmentationProcessSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomFragmentationProcessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomFragmentationProcessSchemasBudgetCertificate.controlled,
      sampleRandomFragmentationProcessSchemasBudgetCertificate]
  · norm_num [RandomFragmentationProcessSchemasBudgetCertificate.budgetControlled,
      sampleRandomFragmentationProcessSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomFragmentationProcessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomFragmentationProcessSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomFragmentationProcessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomFragmentationProcessSchemasBudgetCertificate.controlled,
      sampleRandomFragmentationProcessSchemasBudgetCertificate]
  · norm_num [RandomFragmentationProcessSchemasBudgetCertificate.budgetControlled,
      sampleRandomFragmentationProcessSchemasBudgetCertificate]

example :
    sampleRandomFragmentationProcessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomFragmentationProcessSchemasBudgetCertificate.size := by
  apply randomFragmentationProcessSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomFragmentationProcessSchemasBudgetCertificate.controlled,
      sampleRandomFragmentationProcessSchemasBudgetCertificate]
  · norm_num [RandomFragmentationProcessSchemasBudgetCertificate.budgetControlled,
      sampleRandomFragmentationProcessSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomFragmentationProcessSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomFragmentationProcessSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomFragmentationProcessSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomFragmentationProcessSchemas
