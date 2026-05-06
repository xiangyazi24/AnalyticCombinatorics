import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite Boltzmann pointing models.

This module records finite bookkeeping for pointed Boltzmann samplers.
-/

namespace AnalyticCombinatorics.AppA.FiniteBoltzmannPointingModels

structure BoltzmannPointingData where
  samplerStates : ℕ
  pointingChoices : ℕ
  samplerSlack : ℕ
deriving DecidableEq, Repr

def hasSamplerStates (d : BoltzmannPointingData) : Prop :=
  0 < d.samplerStates

def pointingChoicesControlled (d : BoltzmannPointingData) : Prop :=
  d.pointingChoices ≤ d.samplerStates + d.samplerSlack

def boltzmannPointingReady (d : BoltzmannPointingData) : Prop :=
  hasSamplerStates d ∧ pointingChoicesControlled d

def boltzmannPointingBudget (d : BoltzmannPointingData) : ℕ :=
  d.samplerStates + d.pointingChoices + d.samplerSlack

theorem boltzmannPointingReady.hasSamplerStates
    {d : BoltzmannPointingData}
    (h : boltzmannPointingReady d) :
    hasSamplerStates d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem pointingChoices_le_budget (d : BoltzmannPointingData) :
    d.pointingChoices ≤ boltzmannPointingBudget d := by
  unfold boltzmannPointingBudget
  omega

def sampleBoltzmannPointingData : BoltzmannPointingData :=
  { samplerStates := 6, pointingChoices := 8, samplerSlack := 3 }

example : boltzmannPointingReady sampleBoltzmannPointingData := by
  norm_num [boltzmannPointingReady, hasSamplerStates]
  norm_num [pointingChoicesControlled, sampleBoltzmannPointingData]

example : boltzmannPointingBudget sampleBoltzmannPointingData = 17 := by
  native_decide

structure BoltzmannPointingWindow where
  samplerStates : ℕ
  pointingChoices : ℕ
  samplerSlack : ℕ
  oracleBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoltzmannPointingWindow.pointingControlled (w : BoltzmannPointingWindow) : Prop :=
  w.pointingChoices ≤ w.samplerStates + w.samplerSlack + w.slack

def BoltzmannPointingWindow.oracleControlled (w : BoltzmannPointingWindow) : Prop :=
  w.oracleBudget ≤ w.samplerStates + w.pointingChoices + w.samplerSlack + w.slack

def boltzmannPointingWindowReady (w : BoltzmannPointingWindow) : Prop :=
  0 < w.samplerStates ∧
    w.pointingControlled ∧
    w.oracleControlled

def BoltzmannPointingWindow.certificate (w : BoltzmannPointingWindow) : ℕ :=
  w.samplerStates + w.pointingChoices + w.samplerSlack + w.slack

theorem boltzmannPointing_oracleBudget_le_certificate {w : BoltzmannPointingWindow}
    (h : boltzmannPointingWindowReady w) :
    w.oracleBudget ≤ w.certificate := by
  rcases h with ⟨_, _, horacle⟩
  exact horacle

def sampleBoltzmannPointingWindow : BoltzmannPointingWindow :=
  { samplerStates := 6, pointingChoices := 8, samplerSlack := 3, oracleBudget := 16, slack := 0 }

example : boltzmannPointingWindowReady sampleBoltzmannPointingWindow := by
  norm_num [boltzmannPointingWindowReady, BoltzmannPointingWindow.pointingControlled,
    BoltzmannPointingWindow.oracleControlled, sampleBoltzmannPointingWindow]

example : sampleBoltzmannPointingWindow.certificate = 17 := by
  native_decide


structure FiniteBoltzmannPointingModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteBoltzmannPointingModelsBudgetCertificate.controlled
    (c : FiniteBoltzmannPointingModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteBoltzmannPointingModelsBudgetCertificate.budgetControlled
    (c : FiniteBoltzmannPointingModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteBoltzmannPointingModelsBudgetCertificate.Ready
    (c : FiniteBoltzmannPointingModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteBoltzmannPointingModelsBudgetCertificate.size
    (c : FiniteBoltzmannPointingModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteBoltzmannPointingModels_budgetCertificate_le_size
    (c : FiniteBoltzmannPointingModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteBoltzmannPointingModelsBudgetCertificate :
    FiniteBoltzmannPointingModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteBoltzmannPointingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteBoltzmannPointingModelsBudgetCertificate.controlled,
      sampleFiniteBoltzmannPointingModelsBudgetCertificate]
  · norm_num [FiniteBoltzmannPointingModelsBudgetCertificate.budgetControlled,
      sampleFiniteBoltzmannPointingModelsBudgetCertificate]

example :
    sampleFiniteBoltzmannPointingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteBoltzmannPointingModelsBudgetCertificate.size := by
  apply finiteBoltzmannPointingModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteBoltzmannPointingModelsBudgetCertificate.controlled,
      sampleFiniteBoltzmannPointingModelsBudgetCertificate]
  · norm_num [FiniteBoltzmannPointingModelsBudgetCertificate.budgetControlled,
      sampleFiniteBoltzmannPointingModelsBudgetCertificate]

/-- Finite executable readiness audit for Boltzmann-pointing certificates. -/
def finiteBoltzmannPointingModelsBudgetCertificateListReady
    (data : List FiniteBoltzmannPointingModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteBoltzmannPointingModelsBudgetCertificateList_readyWindow :
    finiteBoltzmannPointingModelsBudgetCertificateListReady
      [sampleFiniteBoltzmannPointingModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold finiteBoltzmannPointingModelsBudgetCertificateListReady
    sampleFiniteBoltzmannPointingModelsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteBoltzmannPointingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteBoltzmannPointingModelsBudgetCertificate.controlled,
      sampleFiniteBoltzmannPointingModelsBudgetCertificate]
  · norm_num [FiniteBoltzmannPointingModelsBudgetCertificate.budgetControlled,
      sampleFiniteBoltzmannPointingModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteBoltzmannPointingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteBoltzmannPointingModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FiniteBoltzmannPointingModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteBoltzmannPointingModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFiniteBoltzmannPointingModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FiniteBoltzmannPointingModels
