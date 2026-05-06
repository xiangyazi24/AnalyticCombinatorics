import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Vague convergence schema bookkeeping.

The finite data records compact support tests and discrepancy budgets.
-/

namespace AnalyticCombinatorics.AppC.VagueConvergenceSchemas

structure VagueConvergenceData where
  compactTestCount : ℕ
  discrepancyBudget : ℕ
  supportRadius : ℕ
deriving DecidableEq, Repr

def nonemptyCompactTests (d : VagueConvergenceData) : Prop :=
  0 < d.compactTestCount

def positiveSupportRadius (d : VagueConvergenceData) : Prop :=
  0 < d.supportRadius

def vagueConvergenceReady (d : VagueConvergenceData) : Prop :=
  nonemptyCompactTests d ∧ positiveSupportRadius d

def vagueConvergenceBudget (d : VagueConvergenceData) : ℕ :=
  d.compactTestCount + d.discrepancyBudget + d.supportRadius

theorem vagueConvergenceReady.tests {d : VagueConvergenceData}
    (h : vagueConvergenceReady d) :
    nonemptyCompactTests d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem compactTestCount_le_budget (d : VagueConvergenceData) :
    d.compactTestCount ≤ vagueConvergenceBudget d := by
  unfold vagueConvergenceBudget
  omega

def sampleVagueConvergence : VagueConvergenceData :=
  { compactTestCount := 4, discrepancyBudget := 2, supportRadius := 7 }

example : vagueConvergenceReady sampleVagueConvergence := by
  norm_num
    [vagueConvergenceReady, nonemptyCompactTests, positiveSupportRadius,
      sampleVagueConvergence]

example : vagueConvergenceBudget sampleVagueConvergence = 13 := by
  native_decide

structure VagueConvergenceWindow where
  compactTestCount : ℕ
  discrepancyBudget : ℕ
  supportRadius : ℕ
  localizationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def VagueConvergenceWindow.discrepancyControlled (w : VagueConvergenceWindow) : Prop :=
  w.discrepancyBudget ≤ w.compactTestCount + w.supportRadius + w.slack

def VagueConvergenceWindow.localizationControlled (w : VagueConvergenceWindow) : Prop :=
  w.localizationBudget ≤ w.compactTestCount + w.discrepancyBudget + w.supportRadius + w.slack

def vagueConvergenceWindowReady (w : VagueConvergenceWindow) : Prop :=
  0 < w.compactTestCount ∧
    0 < w.supportRadius ∧
    w.discrepancyControlled ∧
    w.localizationControlled

def VagueConvergenceWindow.certificate (w : VagueConvergenceWindow) : ℕ :=
  w.compactTestCount + w.discrepancyBudget + w.supportRadius + w.slack

theorem vagueConvergence_localizationBudget_le_certificate {w : VagueConvergenceWindow}
    (h : vagueConvergenceWindowReady w) :
    w.localizationBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hlocal⟩
  exact hlocal

def sampleVagueConvergenceWindow : VagueConvergenceWindow :=
  { compactTestCount := 4, discrepancyBudget := 2, supportRadius := 7, localizationBudget := 12,
    slack := 0 }

example : vagueConvergenceWindowReady sampleVagueConvergenceWindow := by
  norm_num [vagueConvergenceWindowReady, VagueConvergenceWindow.discrepancyControlled,
    VagueConvergenceWindow.localizationControlled, sampleVagueConvergenceWindow]

example : sampleVagueConvergenceWindow.certificate = 13 := by
  native_decide


structure VagueConvergenceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def VagueConvergenceSchemasBudgetCertificate.controlled
    (c : VagueConvergenceSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def VagueConvergenceSchemasBudgetCertificate.budgetControlled
    (c : VagueConvergenceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def VagueConvergenceSchemasBudgetCertificate.Ready
    (c : VagueConvergenceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def VagueConvergenceSchemasBudgetCertificate.size
    (c : VagueConvergenceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem vagueConvergenceSchemas_budgetCertificate_le_size
    (c : VagueConvergenceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleVagueConvergenceSchemasBudgetCertificate :
    VagueConvergenceSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleVagueConvergenceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [VagueConvergenceSchemasBudgetCertificate.controlled,
      sampleVagueConvergenceSchemasBudgetCertificate]
  · norm_num [VagueConvergenceSchemasBudgetCertificate.budgetControlled,
      sampleVagueConvergenceSchemasBudgetCertificate]

example : sampleVagueConvergenceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [VagueConvergenceSchemasBudgetCertificate.controlled,
      sampleVagueConvergenceSchemasBudgetCertificate]
  · norm_num [VagueConvergenceSchemasBudgetCertificate.budgetControlled,
      sampleVagueConvergenceSchemasBudgetCertificate]

example :
    sampleVagueConvergenceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleVagueConvergenceSchemasBudgetCertificate.size := by
  apply vagueConvergenceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [VagueConvergenceSchemasBudgetCertificate.controlled,
      sampleVagueConvergenceSchemasBudgetCertificate]
  · norm_num [VagueConvergenceSchemasBudgetCertificate.budgetControlled,
      sampleVagueConvergenceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleVagueConvergenceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleVagueConvergenceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List VagueConvergenceSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleVagueConvergenceSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleVagueConvergenceSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.VagueConvergenceSchemas
