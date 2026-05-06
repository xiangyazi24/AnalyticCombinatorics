import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Uniform Transfer

Finite parameter-uniform checks and schema descriptors.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformTransfer

def uniformBoundCheck (a : ℕ → ℕ → ℕ) (B N K : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    (List.range (K + 1)).all fun k => a n k ≤ B

theorem uniformBoundCheck_samples :
    uniformBoundCheck (fun n k => n + k) 10 4 6 = true ∧
    uniformBoundCheck (fun n k => n * k) 10 4 6 = false := by
  native_decide

def uniformScale (rhoInv n k : ℕ) : ℕ :=
  rhoInv ^ n * (k + 1)

theorem uniformScale_samples :
    uniformScale 2 3 0 = 8 ∧ uniformScale 2 3 2 = 24 := by
  native_decide

structure UniformTransferData where
  parameterBound : ℕ
  radiusInv : ℕ
  exponentDenominator : ℕ

def boundedParameterTransferData : UniformTransferData where
  parameterBound := 10
  radiusInv := 4
  exponentDenominator := 2

theorem boundedParameterTransferData_values :
    boundedParameterTransferData.parameterBound = 10 ∧
    boundedParameterTransferData.radiusInv = 4 ∧
    boundedParameterTransferData.exponentDenominator = 2 := by
  native_decide

def uniformTransferDataReady (data : UniformTransferData) : Prop :=
  0 < data.parameterBound ∧ 0 < data.radiusInv ∧ 0 < data.exponentDenominator

theorem boundedParameterTransferData_ready :
    uniformTransferDataReady boundedParameterTransferData := by
  unfold uniformTransferDataReady boundedParameterTransferData
  native_decide

/-- Finite executable readiness audit for uniform transfer data. -/
def uniformTransferDataListReady (data : List UniformTransferData) : Bool :=
  data.all fun d =>
    0 < d.parameterBound && 0 < d.radiusInv && 0 < d.exponentDenominator

theorem uniformTransferDataList_readyWindow :
    uniformTransferDataListReady
      [boundedParameterTransferData,
       { parameterBound := 8, radiusInv := 3, exponentDenominator := 2 }] = true := by
  unfold uniformTransferDataListReady boundedParameterTransferData
  native_decide

def UniformTransferSchema
    (coeff : ℕ → ℕ → ℂ) (data : UniformTransferData) : Prop :=
  uniformTransferDataReady data ∧ coeff 0 0 = 1 ∧ coeff 3 2 = 24

def uniformTransferCoeffWitness (n k : ℕ) : ℂ :=
  uniformScale 2 n k

theorem uniform_transfer_schema_statement :
    UniformTransferSchema uniformTransferCoeffWitness boundedParameterTransferData := by
  unfold UniformTransferSchema uniformTransferDataReady boundedParameterTransferData
    uniformTransferCoeffWitness uniformScale
  norm_num

/-- A finite certificate for uniform transfer schema data. -/
structure UniformTransferCertificate where
  parameterWindow : ℕ
  radiusWindow : ℕ
  denominatorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Uniform transfer certificates keep all structural parameters positive. -/
def uniformTransferCertificateControlled
    (w : UniformTransferCertificate) : Prop :=
  0 < w.parameterWindow ∧ 0 < w.radiusWindow ∧ 0 < w.denominatorWindow

/-- Readiness for a uniform transfer certificate. -/
def uniformTransferCertificateReady
    (w : UniformTransferCertificate) : Prop :=
  uniformTransferCertificateControlled w ∧
    w.certificateBudget ≤
      w.parameterWindow + w.radiusWindow + w.denominatorWindow + w.slack

/-- Total size of a uniform transfer certificate. -/
def uniformTransferCertificateSize (w : UniformTransferCertificate) : ℕ :=
  w.parameterWindow + w.radiusWindow + w.denominatorWindow +
    w.certificateBudget + w.slack

theorem uniformTransferCertificate_budget_le_size
    (w : UniformTransferCertificate)
    (h : uniformTransferCertificateReady w) :
    w.certificateBudget ≤ uniformTransferCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold uniformTransferCertificateSize
  omega

def sampleUniformTransferCertificate : UniformTransferCertificate where
  parameterWindow := 10
  radiusWindow := 4
  denominatorWindow := 2
  certificateBudget := 15
  slack := 1

example :
    uniformTransferCertificateReady sampleUniformTransferCertificate := by
  norm_num [uniformTransferCertificateReady,
    uniformTransferCertificateControlled, sampleUniformTransferCertificate]

example :
    sampleUniformTransferCertificate.certificateBudget ≤
      uniformTransferCertificateSize sampleUniformTransferCertificate := by
  apply uniformTransferCertificate_budget_le_size
  norm_num [uniformTransferCertificateReady,
    uniformTransferCertificateControlled, sampleUniformTransferCertificate]

structure UniformTransferRefinementCertificate where
  parameterWindow : ℕ
  radiusWindow : ℕ
  denominatorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformTransferRefinementCertificate.parametersControlled
    (c : UniformTransferRefinementCertificate) : Prop :=
  0 < c.parameterWindow ∧ 0 < c.radiusWindow ∧ 0 < c.denominatorWindow

def UniformTransferRefinementCertificate.certificateBudgetControlled
    (c : UniformTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.parameterWindow + c.radiusWindow + c.denominatorWindow + c.slack

def uniformTransferRefinementReady
    (c : UniformTransferRefinementCertificate) : Prop :=
  c.parametersControlled ∧ c.certificateBudgetControlled

def UniformTransferRefinementCertificate.size
    (c : UniformTransferRefinementCertificate) : ℕ :=
  c.parameterWindow + c.radiusWindow + c.denominatorWindow + c.slack

theorem uniformTransfer_certificateBudgetWindow_le_size
    {c : UniformTransferRefinementCertificate}
    (h : uniformTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformTransferRefinementCertificate :
    UniformTransferRefinementCertificate :=
  { parameterWindow := 10, radiusWindow := 4, denominatorWindow := 2,
    certificateBudgetWindow := 17, slack := 1 }

example : uniformTransferRefinementReady
    sampleUniformTransferRefinementCertificate := by
  norm_num [uniformTransferRefinementReady,
    UniformTransferRefinementCertificate.parametersControlled,
    UniformTransferRefinementCertificate.certificateBudgetControlled,
    sampleUniformTransferRefinementCertificate]

example :
    sampleUniformTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformTransferRefinementCertificate.size := by
  norm_num [UniformTransferRefinementCertificate.size,
    sampleUniformTransferRefinementCertificate]

structure UniformTransferBudgetCertificate where
  parameterWindow : ℕ
  radiusWindow : ℕ
  denominatorWindow : ℕ
  transferBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformTransferBudgetCertificate.controlled
    (c : UniformTransferBudgetCertificate) : Prop :=
  0 < c.parameterWindow ∧
    0 < c.radiusWindow ∧
      0 < c.denominatorWindow ∧
        c.transferBudgetWindow ≤
          c.parameterWindow + c.radiusWindow + c.denominatorWindow + c.slack

def UniformTransferBudgetCertificate.budgetControlled
    (c : UniformTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.parameterWindow + c.radiusWindow + c.denominatorWindow +
      c.transferBudgetWindow + c.slack

def UniformTransferBudgetCertificate.Ready
    (c : UniformTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformTransferBudgetCertificate.size
    (c : UniformTransferBudgetCertificate) : ℕ :=
  c.parameterWindow + c.radiusWindow + c.denominatorWindow +
    c.transferBudgetWindow + c.slack

theorem uniformTransfer_budgetCertificate_le_size
    (c : UniformTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformTransferBudgetCertificate :
    UniformTransferBudgetCertificate :=
  { parameterWindow := 10
    radiusWindow := 4
    denominatorWindow := 2
    transferBudgetWindow := 17
    certificateBudgetWindow := 34
    slack := 1 }

example : sampleUniformTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformTransferBudgetCertificate.controlled,
      sampleUniformTransferBudgetCertificate]
  · norm_num [UniformTransferBudgetCertificate.budgetControlled,
      sampleUniformTransferBudgetCertificate]

example :
    sampleUniformTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformTransferBudgetCertificate.size := by
  apply uniformTransfer_budgetCertificate_le_size
  constructor
  · norm_num [UniformTransferBudgetCertificate.controlled,
      sampleUniformTransferBudgetCertificate]
  · norm_num [UniformTransferBudgetCertificate.budgetControlled,
      sampleUniformTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformTransferBudgetCertificate.controlled,
      sampleUniformTransferBudgetCertificate]
  · norm_num [UniformTransferBudgetCertificate.budgetControlled,
      sampleUniformTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformTransfer
