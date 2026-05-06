import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite Boltzmann oracle models.

The finite schema records oracle calls, tuning budget, and rejection
slack for Boltzmann-style samplers.
-/

namespace AnalyticCombinatorics.AppA.FiniteBoltzmannOracleModels

structure BoltzmannOracleData where
  oracleCalls : ℕ
  tuningBudget : ℕ
  rejectionSlack : ℕ
deriving DecidableEq, Repr

def oracleCallsPositive (d : BoltzmannOracleData) : Prop :=
  0 < d.oracleCalls

def tuningControlled (d : BoltzmannOracleData) : Prop :=
  d.tuningBudget ≤ d.oracleCalls + d.rejectionSlack

def boltzmannOracleReady (d : BoltzmannOracleData) : Prop :=
  oracleCallsPositive d ∧ tuningControlled d

def boltzmannOracleBudget (d : BoltzmannOracleData) : ℕ :=
  d.oracleCalls + d.tuningBudget + d.rejectionSlack

theorem boltzmannOracleReady.calls {d : BoltzmannOracleData}
    (h : boltzmannOracleReady d) :
    oracleCallsPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem tuningBudget_le_oracleBudget (d : BoltzmannOracleData) :
    d.tuningBudget ≤ boltzmannOracleBudget d := by
  unfold boltzmannOracleBudget
  omega

def sampleBoltzmannOracleData : BoltzmannOracleData :=
  { oracleCalls := 6, tuningBudget := 8, rejectionSlack := 3 }

example : boltzmannOracleReady sampleBoltzmannOracleData := by
  norm_num [boltzmannOracleReady, oracleCallsPositive]
  norm_num [tuningControlled, sampleBoltzmannOracleData]

example : boltzmannOracleBudget sampleBoltzmannOracleData = 17 := by
  native_decide

structure BoltzmannOracleWindow where
  oracleCalls : ℕ
  tuningBudget : ℕ
  rejectionSlack : ℕ
  queryBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoltzmannOracleWindow.tuningControlled (w : BoltzmannOracleWindow) : Prop :=
  w.tuningBudget ≤ w.oracleCalls + w.rejectionSlack + w.slack

def BoltzmannOracleWindow.queryControlled (w : BoltzmannOracleWindow) : Prop :=
  w.queryBudget ≤ w.oracleCalls + w.tuningBudget + w.rejectionSlack + w.slack

def boltzmannOracleWindowReady (w : BoltzmannOracleWindow) : Prop :=
  0 < w.oracleCalls ∧
    w.tuningControlled ∧
    w.queryControlled

def BoltzmannOracleWindow.certificate (w : BoltzmannOracleWindow) : ℕ :=
  w.oracleCalls + w.tuningBudget + w.rejectionSlack + w.slack

theorem boltzmannOracle_queryBudget_le_certificate {w : BoltzmannOracleWindow}
    (h : boltzmannOracleWindowReady w) :
    w.queryBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hquery⟩
  exact hquery

def sampleBoltzmannOracleWindow : BoltzmannOracleWindow :=
  { oracleCalls := 6, tuningBudget := 8, rejectionSlack := 3, queryBudget := 15, slack := 0 }

example : boltzmannOracleWindowReady sampleBoltzmannOracleWindow := by
  norm_num [boltzmannOracleWindowReady, BoltzmannOracleWindow.tuningControlled,
    BoltzmannOracleWindow.queryControlled, sampleBoltzmannOracleWindow]

example : sampleBoltzmannOracleWindow.certificate = 17 := by
  native_decide


structure FiniteBoltzmannOracleModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteBoltzmannOracleModelsBudgetCertificate.controlled
    (c : FiniteBoltzmannOracleModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteBoltzmannOracleModelsBudgetCertificate.budgetControlled
    (c : FiniteBoltzmannOracleModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteBoltzmannOracleModelsBudgetCertificate.Ready
    (c : FiniteBoltzmannOracleModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteBoltzmannOracleModelsBudgetCertificate.size
    (c : FiniteBoltzmannOracleModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteBoltzmannOracleModels_budgetCertificate_le_size
    (c : FiniteBoltzmannOracleModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteBoltzmannOracleModelsBudgetCertificate :
    FiniteBoltzmannOracleModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteBoltzmannOracleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteBoltzmannOracleModelsBudgetCertificate.controlled,
      sampleFiniteBoltzmannOracleModelsBudgetCertificate]
  · norm_num [FiniteBoltzmannOracleModelsBudgetCertificate.budgetControlled,
      sampleFiniteBoltzmannOracleModelsBudgetCertificate]

example :
    sampleFiniteBoltzmannOracleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteBoltzmannOracleModelsBudgetCertificate.size := by
  apply finiteBoltzmannOracleModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteBoltzmannOracleModelsBudgetCertificate.controlled,
      sampleFiniteBoltzmannOracleModelsBudgetCertificate]
  · norm_num [FiniteBoltzmannOracleModelsBudgetCertificate.budgetControlled,
      sampleFiniteBoltzmannOracleModelsBudgetCertificate]

/-- Finite executable readiness audit for Boltzmann-oracle certificates. -/
def finiteBoltzmannOracleModelsBudgetCertificateListReady
    (data : List FiniteBoltzmannOracleModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteBoltzmannOracleModelsBudgetCertificateList_readyWindow :
    finiteBoltzmannOracleModelsBudgetCertificateListReady
      [sampleFiniteBoltzmannOracleModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold finiteBoltzmannOracleModelsBudgetCertificateListReady
    sampleFiniteBoltzmannOracleModelsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteBoltzmannOracleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteBoltzmannOracleModelsBudgetCertificate.controlled,
      sampleFiniteBoltzmannOracleModelsBudgetCertificate]
  · norm_num [FiniteBoltzmannOracleModelsBudgetCertificate.budgetControlled,
      sampleFiniteBoltzmannOracleModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteBoltzmannOracleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteBoltzmannOracleModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FiniteBoltzmannOracleModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteBoltzmannOracleModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFiniteBoltzmannOracleModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FiniteBoltzmannOracleModels
