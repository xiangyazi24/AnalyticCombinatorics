import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Perron window schemas.

The finite record stores Perron height, abscissa window, and truncation
slack.
-/

namespace AnalyticCombinatorics.PartB.Ch5.PerronWindowSchemas

structure PerronWindowData where
  perronHeight : ℕ
  abscissaWindow : ℕ
  truncationSlack : ℕ
deriving DecidableEq, Repr

def perronHeightPositive (d : PerronWindowData) : Prop :=
  0 < d.perronHeight

def abscissaWindowControlled (d : PerronWindowData) : Prop :=
  d.abscissaWindow ≤ d.perronHeight + d.truncationSlack

def perronWindowReady (d : PerronWindowData) : Prop :=
  perronHeightPositive d ∧ abscissaWindowControlled d

def perronWindowBudget (d : PerronWindowData) : ℕ :=
  d.perronHeight + d.abscissaWindow + d.truncationSlack

theorem perronWindowReady.height {d : PerronWindowData}
    (h : perronWindowReady d) :
    perronHeightPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem abscissaWindow_le_perronWindowBudget (d : PerronWindowData) :
    d.abscissaWindow ≤ perronWindowBudget d := by
  unfold perronWindowBudget
  omega

def samplePerronWindowData : PerronWindowData :=
  { perronHeight := 6, abscissaWindow := 8, truncationSlack := 3 }

example : perronWindowReady samplePerronWindowData := by
  norm_num [perronWindowReady, perronHeightPositive]
  norm_num [abscissaWindowControlled, samplePerronWindowData]

example : perronWindowBudget samplePerronWindowData = 17 := by
  native_decide

structure PerronCertificateWindow where
  perronHeight : ℕ
  abscissaWindow : ℕ
  truncationSlack : ℕ
  integralBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PerronCertificateWindow.abscissaControlled (w : PerronCertificateWindow) : Prop :=
  w.abscissaWindow ≤ w.perronHeight + w.truncationSlack + w.slack

def PerronCertificateWindow.integralControlled (w : PerronCertificateWindow) : Prop :=
  w.integralBudget ≤ w.perronHeight + w.abscissaWindow + w.truncationSlack + w.slack

def perronCertificateReady (w : PerronCertificateWindow) : Prop :=
  0 < w.perronHeight ∧
    w.abscissaControlled ∧
    w.integralControlled

def PerronCertificateWindow.certificate (w : PerronCertificateWindow) : ℕ :=
  w.perronHeight + w.abscissaWindow + w.truncationSlack + w.slack

theorem perron_integralBudget_le_certificate {w : PerronCertificateWindow}
    (h : perronCertificateReady w) :
    w.integralBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hintegral⟩
  exact hintegral

def samplePerronCertificateWindow : PerronCertificateWindow :=
  { perronHeight := 6, abscissaWindow := 8, truncationSlack := 3, integralBudget := 16,
    slack := 0 }

example : perronCertificateReady samplePerronCertificateWindow := by
  norm_num [perronCertificateReady, PerronCertificateWindow.abscissaControlled,
    PerronCertificateWindow.integralControlled, samplePerronCertificateWindow]

example : samplePerronCertificateWindow.certificate = 17 := by
  native_decide


structure PerronWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PerronWindowSchemasBudgetCertificate.controlled
    (c : PerronWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PerronWindowSchemasBudgetCertificate.budgetControlled
    (c : PerronWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PerronWindowSchemasBudgetCertificate.Ready
    (c : PerronWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PerronWindowSchemasBudgetCertificate.size
    (c : PerronWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem perronWindowSchemas_budgetCertificate_le_size
    (c : PerronWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePerronWindowSchemasBudgetCertificate :
    PerronWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePerronWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PerronWindowSchemasBudgetCertificate.controlled,
      samplePerronWindowSchemasBudgetCertificate]
  · norm_num [PerronWindowSchemasBudgetCertificate.budgetControlled,
      samplePerronWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePerronWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePerronWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePerronWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PerronWindowSchemasBudgetCertificate.controlled,
      samplePerronWindowSchemasBudgetCertificate]
  · norm_num [PerronWindowSchemasBudgetCertificate.budgetControlled,
      samplePerronWindowSchemasBudgetCertificate]

example :
    samplePerronWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePerronWindowSchemasBudgetCertificate.size := by
  apply perronWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PerronWindowSchemasBudgetCertificate.controlled,
      samplePerronWindowSchemasBudgetCertificate]
  · norm_num [PerronWindowSchemasBudgetCertificate.budgetControlled,
      samplePerronWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PerronWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePerronWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePerronWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.PerronWindowSchemas
