import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Fragmentation limit schema bookkeeping.

The data records split count, mass preservation, and variance budget for
fragmentation-coalescence examples.
-/

namespace AnalyticCombinatorics.PartB.Ch9.FragmentationLimitSchemas

structure FragmentationData where
  initialMass : ℕ
  fragmentCount : ℕ
  varianceBudget : ℕ
deriving DecidableEq, Repr

def nontrivialFragmentation (d : FragmentationData) : Prop :=
  0 < d.initialMass ∧ 1 < d.fragmentCount

def varianceControlled (d : FragmentationData) : Prop :=
  0 < d.varianceBudget

def fragmentationReady (d : FragmentationData) : Prop :=
  nontrivialFragmentation d ∧ varianceControlled d

def averageMassDenominator (d : FragmentationData) : ℕ :=
  d.fragmentCount

theorem fragmentationReady.nontrivial {d : FragmentationData}
    (h : fragmentationReady d) :
    nontrivialFragmentation d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem averageMassDenominator_positive {d : FragmentationData}
    (h : nontrivialFragmentation d) :
    0 < averageMassDenominator d := by
  unfold averageMassDenominator nontrivialFragmentation at *
  omega

def sampleFragmentation : FragmentationData :=
  { initialMass := 12, fragmentCount := 3, varianceBudget := 5 }

example : fragmentationReady sampleFragmentation := by
  norm_num [fragmentationReady, nontrivialFragmentation, varianceControlled, sampleFragmentation]

example : averageMassDenominator sampleFragmentation = 3 := by
  native_decide

/-- Finite executable readiness audit for fragmentation limit data. -/
def fragmentationDataListReady
    (data : List FragmentationData) : Bool :=
  data.all fun d =>
    0 < d.initialMass && 1 < d.fragmentCount && 0 < d.varianceBudget

theorem fragmentationDataList_readyWindow :
    fragmentationDataListReady
      [{ initialMass := 8, fragmentCount := 2, varianceBudget := 3 },
       { initialMass := 12, fragmentCount := 3, varianceBudget := 5 }] = true := by
  unfold fragmentationDataListReady
  native_decide

structure FragmentationWindow where
  initialMass : ℕ
  fragmentCount : ℕ
  varianceBudget : ℕ
  splitBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FragmentationWindow.splitControlled (w : FragmentationWindow) : Prop :=
  w.splitBudget ≤ w.initialMass + w.fragmentCount + w.varianceBudget + w.slack

def fragmentationWindowReady (w : FragmentationWindow) : Prop :=
  0 < w.initialMass ∧
    1 < w.fragmentCount ∧
    0 < w.varianceBudget ∧
    w.splitControlled

def FragmentationWindow.certificate (w : FragmentationWindow) : ℕ :=
  w.initialMass + w.fragmentCount + w.varianceBudget + w.slack

theorem fragmentation_splitBudget_le_certificate {w : FragmentationWindow}
    (h : fragmentationWindowReady w) :
    w.splitBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hsplit⟩
  exact hsplit

def sampleFragmentationWindow : FragmentationWindow :=
  { initialMass := 12, fragmentCount := 3, varianceBudget := 5, splitBudget := 19, slack := 0 }

example : fragmentationWindowReady sampleFragmentationWindow := by
  norm_num [fragmentationWindowReady, FragmentationWindow.splitControlled,
    sampleFragmentationWindow]

example : sampleFragmentationWindow.certificate = 20 := by
  native_decide


structure FragmentationLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FragmentationLimitSchemasBudgetCertificate.controlled
    (c : FragmentationLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FragmentationLimitSchemasBudgetCertificate.budgetControlled
    (c : FragmentationLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FragmentationLimitSchemasBudgetCertificate.Ready
    (c : FragmentationLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FragmentationLimitSchemasBudgetCertificate.size
    (c : FragmentationLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem fragmentationLimitSchemas_budgetCertificate_le_size
    (c : FragmentationLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFragmentationLimitSchemasBudgetCertificate :
    FragmentationLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFragmentationLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [FragmentationLimitSchemasBudgetCertificate.controlled,
      sampleFragmentationLimitSchemasBudgetCertificate]
  · norm_num [FragmentationLimitSchemasBudgetCertificate.budgetControlled,
      sampleFragmentationLimitSchemasBudgetCertificate]

example :
    sampleFragmentationLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleFragmentationLimitSchemasBudgetCertificate.size := by
  apply fragmentationLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [FragmentationLimitSchemasBudgetCertificate.controlled,
      sampleFragmentationLimitSchemasBudgetCertificate]
  · norm_num [FragmentationLimitSchemasBudgetCertificate.budgetControlled,
      sampleFragmentationLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFragmentationLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [FragmentationLimitSchemasBudgetCertificate.controlled,
      sampleFragmentationLimitSchemasBudgetCertificate]
  · norm_num [FragmentationLimitSchemasBudgetCertificate.budgetControlled,
      sampleFragmentationLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFragmentationLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleFragmentationLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FragmentationLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFragmentationLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFragmentationLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.FragmentationLimitSchemas
