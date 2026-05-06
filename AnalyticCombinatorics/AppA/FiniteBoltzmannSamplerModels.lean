import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite Boltzmann sampler models.

The finite record stores tuning, rejection, and output-size budgets for
sampler bookkeeping.
-/

namespace AnalyticCombinatorics.AppA.FiniteBoltzmannSamplerModels

structure BoltzmannSamplerData where
  tuningBudget : ℕ
  rejectionBudget : ℕ
  outputBudget : ℕ
deriving DecidableEq, Repr

def tuningPositive (d : BoltzmannSamplerData) : Prop :=
  0 < d.tuningBudget

def rejectionControlled (d : BoltzmannSamplerData) : Prop :=
  d.rejectionBudget ≤ d.tuningBudget + d.outputBudget

def boltzmannSamplerReady (d : BoltzmannSamplerData) : Prop :=
  tuningPositive d ∧ rejectionControlled d

def boltzmannSamplerBudget (d : BoltzmannSamplerData) : ℕ :=
  d.tuningBudget + d.rejectionBudget + d.outputBudget

theorem boltzmannSamplerReady.tuning {d : BoltzmannSamplerData}
    (h : boltzmannSamplerReady d) :
    tuningPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem outputBudget_le_samplerBudget (d : BoltzmannSamplerData) :
    d.outputBudget ≤ boltzmannSamplerBudget d := by
  unfold boltzmannSamplerBudget
  omega

def sampleBoltzmannSamplerData : BoltzmannSamplerData :=
  { tuningBudget := 6, rejectionBudget := 8, outputBudget := 3 }

example : boltzmannSamplerReady sampleBoltzmannSamplerData := by
  norm_num [boltzmannSamplerReady, tuningPositive]
  norm_num [rejectionControlled, sampleBoltzmannSamplerData]

example : boltzmannSamplerBudget sampleBoltzmannSamplerData = 17 := by
  native_decide

structure BoltzmannSamplerWindow where
  tuningBudget : ℕ
  rejectionBudget : ℕ
  outputBudget : ℕ
  drawBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoltzmannSamplerWindow.rejectionControlled (w : BoltzmannSamplerWindow) : Prop :=
  w.rejectionBudget ≤ w.tuningBudget + w.outputBudget + w.slack

def BoltzmannSamplerWindow.drawControlled (w : BoltzmannSamplerWindow) : Prop :=
  w.drawBudget ≤ w.tuningBudget + w.rejectionBudget + w.outputBudget + w.slack

def boltzmannSamplerWindowReady (w : BoltzmannSamplerWindow) : Prop :=
  0 < w.tuningBudget ∧
    w.rejectionControlled ∧
    w.drawControlled

def BoltzmannSamplerWindow.certificate (w : BoltzmannSamplerWindow) : ℕ :=
  w.tuningBudget + w.rejectionBudget + w.outputBudget + w.slack

theorem boltzmannSampler_drawBudget_le_certificate {w : BoltzmannSamplerWindow}
    (h : boltzmannSamplerWindowReady w) :
    w.drawBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hdraw⟩
  exact hdraw

def sampleBoltzmannSamplerWindow : BoltzmannSamplerWindow :=
  { tuningBudget := 6, rejectionBudget := 8, outputBudget := 3, drawBudget := 16, slack := 0 }

example : boltzmannSamplerWindowReady sampleBoltzmannSamplerWindow := by
  norm_num [boltzmannSamplerWindowReady, BoltzmannSamplerWindow.rejectionControlled,
    BoltzmannSamplerWindow.drawControlled, sampleBoltzmannSamplerWindow]

example : sampleBoltzmannSamplerWindow.certificate = 17 := by
  native_decide


structure FiniteBoltzmannSamplerModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteBoltzmannSamplerModelsBudgetCertificate.controlled
    (c : FiniteBoltzmannSamplerModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteBoltzmannSamplerModelsBudgetCertificate.budgetControlled
    (c : FiniteBoltzmannSamplerModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteBoltzmannSamplerModelsBudgetCertificate.Ready
    (c : FiniteBoltzmannSamplerModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteBoltzmannSamplerModelsBudgetCertificate.size
    (c : FiniteBoltzmannSamplerModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteBoltzmannSamplerModels_budgetCertificate_le_size
    (c : FiniteBoltzmannSamplerModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteBoltzmannSamplerModelsBudgetCertificate :
    FiniteBoltzmannSamplerModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteBoltzmannSamplerModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteBoltzmannSamplerModelsBudgetCertificate.controlled,
      sampleFiniteBoltzmannSamplerModelsBudgetCertificate]
  · norm_num [FiniteBoltzmannSamplerModelsBudgetCertificate.budgetControlled,
      sampleFiniteBoltzmannSamplerModelsBudgetCertificate]

example :
    sampleFiniteBoltzmannSamplerModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteBoltzmannSamplerModelsBudgetCertificate.size := by
  apply finiteBoltzmannSamplerModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteBoltzmannSamplerModelsBudgetCertificate.controlled,
      sampleFiniteBoltzmannSamplerModelsBudgetCertificate]
  · norm_num [FiniteBoltzmannSamplerModelsBudgetCertificate.budgetControlled,
      sampleFiniteBoltzmannSamplerModelsBudgetCertificate]

/-- Finite executable readiness audit for Boltzmann-sampler certificates. -/
def finiteBoltzmannSamplerModelsBudgetCertificateListReady
    (data : List FiniteBoltzmannSamplerModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteBoltzmannSamplerModelsBudgetCertificateList_readyWindow :
    finiteBoltzmannSamplerModelsBudgetCertificateListReady
      [sampleFiniteBoltzmannSamplerModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold finiteBoltzmannSamplerModelsBudgetCertificateListReady
    sampleFiniteBoltzmannSamplerModelsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteBoltzmannSamplerModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteBoltzmannSamplerModelsBudgetCertificate.controlled,
      sampleFiniteBoltzmannSamplerModelsBudgetCertificate]
  · norm_num [FiniteBoltzmannSamplerModelsBudgetCertificate.budgetControlled,
      sampleFiniteBoltzmannSamplerModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteBoltzmannSamplerModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteBoltzmannSamplerModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FiniteBoltzmannSamplerModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteBoltzmannSamplerModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFiniteBoltzmannSamplerModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FiniteBoltzmannSamplerModels
