import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Singular perturbation schema bookkeeping.

The finite record tracks small parameter, boundary layer width, and residual
error budget.
-/

namespace AnalyticCombinatorics.Asymptotics.SingularPerturbationSchemas

structure SingularPerturbationData where
  smallParameterScale : ℕ
  boundaryLayerWidth : ℕ
  residualError : ℕ
deriving DecidableEq, Repr

def positiveSmallScale (d : SingularPerturbationData) : Prop :=
  0 < d.smallParameterScale

def positiveBoundaryLayer (d : SingularPerturbationData) : Prop :=
  0 < d.boundaryLayerWidth

def singularPerturbationReady (d : SingularPerturbationData) : Prop :=
  positiveSmallScale d ∧ positiveBoundaryLayer d

def singularPerturbationBudget (d : SingularPerturbationData) : ℕ :=
  d.smallParameterScale + d.boundaryLayerWidth + d.residualError

theorem singularPerturbationReady.layer {d : SingularPerturbationData}
    (h : singularPerturbationReady d) :
    positiveSmallScale d ∧ positiveBoundaryLayer d ∧
      d.smallParameterScale ≤ singularPerturbationBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold singularPerturbationBudget
  omega

theorem smallScale_le_budget (d : SingularPerturbationData) :
    d.smallParameterScale ≤ singularPerturbationBudget d := by
  unfold singularPerturbationBudget
  omega

def sampleSingularPerturbation : SingularPerturbationData :=
  { smallParameterScale := 2, boundaryLayerWidth := 7, residualError := 3 }

example : singularPerturbationReady sampleSingularPerturbation := by
  norm_num
    [singularPerturbationReady, positiveSmallScale, positiveBoundaryLayer,
      sampleSingularPerturbation]

example : singularPerturbationBudget sampleSingularPerturbation = 12 := by
  native_decide

/-- Finite executable readiness audit for singular perturbation data. -/
def singularPerturbationDataListReady
    (data : List SingularPerturbationData) : Bool :=
  data.all fun d => 0 < d.smallParameterScale && 0 < d.boundaryLayerWidth

theorem singularPerturbationDataList_readyWindow :
    singularPerturbationDataListReady
      [{ smallParameterScale := 1, boundaryLayerWidth := 3, residualError := 2 },
       { smallParameterScale := 2, boundaryLayerWidth := 7, residualError := 3 }] =
      true := by
  unfold singularPerturbationDataListReady
  native_decide

/-- A certificate window for singular perturbation schemas. -/
structure SingularPerturbationCertificateWindow where
  smallScaleWindow : ℕ
  boundaryWindow : ℕ
  residualWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Boundary and residual windows are controlled by the small scale. -/
def singularPerturbationCertificateControlled
    (w : SingularPerturbationCertificateWindow) : Prop :=
  w.boundaryWindow ≤ w.smallScaleWindow + w.residualWindow + w.slack

/-- Readiness for a singular perturbation certificate. -/
def singularPerturbationCertificateReady
    (w : SingularPerturbationCertificateWindow) : Prop :=
  0 < w.smallScaleWindow ∧
    0 < w.boundaryWindow ∧
      singularPerturbationCertificateControlled w ∧
        w.certificateBudget ≤
          w.smallScaleWindow + w.boundaryWindow + w.residualWindow + w.slack

/-- Total size of a singular perturbation certificate. -/
def singularPerturbationCertificate
    (w : SingularPerturbationCertificateWindow) : ℕ :=
  w.smallScaleWindow + w.boundaryWindow + w.residualWindow +
    w.certificateBudget + w.slack

theorem singularPerturbationCertificate_budget_le_certificate
    (w : SingularPerturbationCertificateWindow)
    (h : singularPerturbationCertificateReady w) :
    w.certificateBudget ≤ singularPerturbationCertificate w := by
  rcases h with ⟨_, _, _, hbudget⟩
  unfold singularPerturbationCertificate
  omega

def sampleSingularPerturbationCertificateWindow :
    SingularPerturbationCertificateWindow where
  smallScaleWindow := 3
  boundaryWindow := 6
  residualWindow := 2
  certificateBudget := 10
  slack := 1

example :
    singularPerturbationCertificateReady
      sampleSingularPerturbationCertificateWindow := by
  norm_num [singularPerturbationCertificateReady,
    singularPerturbationCertificateControlled,
    sampleSingularPerturbationCertificateWindow]

example :
    sampleSingularPerturbationCertificateWindow.certificateBudget ≤
      singularPerturbationCertificate
        sampleSingularPerturbationCertificateWindow := by
  apply singularPerturbationCertificate_budget_le_certificate
  norm_num [singularPerturbationCertificateReady,
    singularPerturbationCertificateControlled,
    sampleSingularPerturbationCertificateWindow]

structure SingularPerturbationRefinementCertificate where
  smallScaleWindow : ℕ
  boundaryWindow : ℕ
  residualWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularPerturbationRefinementCertificate.boundaryControlled
    (c : SingularPerturbationRefinementCertificate) : Prop :=
  c.boundaryWindow ≤ c.smallScaleWindow + c.residualWindow + c.slack

def SingularPerturbationRefinementCertificate.certificateBudgetControlled
    (c : SingularPerturbationRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.smallScaleWindow + c.boundaryWindow + c.residualWindow + c.slack

def singularPerturbationRefinementReady
    (c : SingularPerturbationRefinementCertificate) : Prop :=
  0 < c.smallScaleWindow ∧
    0 < c.boundaryWindow ∧
    c.boundaryControlled ∧
    c.certificateBudgetControlled

def SingularPerturbationRefinementCertificate.size
    (c : SingularPerturbationRefinementCertificate) : ℕ :=
  c.smallScaleWindow + c.boundaryWindow + c.residualWindow + c.slack

theorem singularPerturbation_certificateBudgetWindow_le_size
    {c : SingularPerturbationRefinementCertificate}
    (h : singularPerturbationRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, _, hbudget⟩
  exact hbudget

def sampleSingularPerturbationRefinementCertificate :
    SingularPerturbationRefinementCertificate :=
  { smallScaleWindow := 3, boundaryWindow := 6, residualWindow := 2,
    certificateBudgetWindow := 12, slack := 1 }

example : singularPerturbationRefinementReady
    sampleSingularPerturbationRefinementCertificate := by
  norm_num [singularPerturbationRefinementReady,
    SingularPerturbationRefinementCertificate.boundaryControlled,
    SingularPerturbationRefinementCertificate.certificateBudgetControlled,
    sampleSingularPerturbationRefinementCertificate]

example :
    sampleSingularPerturbationRefinementCertificate.certificateBudgetWindow ≤
      sampleSingularPerturbationRefinementCertificate.size := by
  norm_num [SingularPerturbationRefinementCertificate.size,
    sampleSingularPerturbationRefinementCertificate]

structure SingularPerturbationBudgetCertificate where
  smallScaleWindow : ℕ
  boundaryWindow : ℕ
  residualWindow : ℕ
  perturbationBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularPerturbationBudgetCertificate.controlled
    (c : SingularPerturbationBudgetCertificate) : Prop :=
  0 < c.smallScaleWindow ∧
    0 < c.boundaryWindow ∧
      c.boundaryWindow ≤ c.smallScaleWindow + c.residualWindow + c.slack ∧
        c.perturbationBudgetWindow ≤
          c.smallScaleWindow + c.boundaryWindow + c.residualWindow + c.slack

def SingularPerturbationBudgetCertificate.budgetControlled
    (c : SingularPerturbationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.smallScaleWindow + c.boundaryWindow + c.residualWindow +
      c.perturbationBudgetWindow + c.slack

def SingularPerturbationBudgetCertificate.Ready
    (c : SingularPerturbationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularPerturbationBudgetCertificate.size
    (c : SingularPerturbationBudgetCertificate) : ℕ :=
  c.smallScaleWindow + c.boundaryWindow + c.residualWindow +
    c.perturbationBudgetWindow + c.slack

theorem singularPerturbation_budgetCertificate_le_size
    (c : SingularPerturbationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularPerturbationBudgetCertificate :
    SingularPerturbationBudgetCertificate :=
  { smallScaleWindow := 3
    boundaryWindow := 6
    residualWindow := 2
    perturbationBudgetWindow := 12
    certificateBudgetWindow := 24
    slack := 1 }

example : sampleSingularPerturbationBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularPerturbationBudgetCertificate.controlled,
      sampleSingularPerturbationBudgetCertificate]
  · norm_num [SingularPerturbationBudgetCertificate.budgetControlled,
      sampleSingularPerturbationBudgetCertificate]

example :
    sampleSingularPerturbationBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularPerturbationBudgetCertificate.size := by
  apply singularPerturbation_budgetCertificate_le_size
  constructor
  · norm_num [SingularPerturbationBudgetCertificate.controlled,
      sampleSingularPerturbationBudgetCertificate]
  · norm_num [SingularPerturbationBudgetCertificate.budgetControlled,
      sampleSingularPerturbationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularPerturbationBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularPerturbationBudgetCertificate.controlled,
      sampleSingularPerturbationBudgetCertificate]
  · norm_num [SingularPerturbationBudgetCertificate.budgetControlled,
      sampleSingularPerturbationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularPerturbationBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularPerturbationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SingularPerturbationBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularPerturbationBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSingularPerturbationBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SingularPerturbationSchemas
