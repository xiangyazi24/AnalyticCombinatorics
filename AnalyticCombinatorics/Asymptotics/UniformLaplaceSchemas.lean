import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Laplace schema bookkeeping.

The finite data records uniform window size, curvature, and remainder
budgets.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformLaplaceSchemas

structure UniformLaplaceData where
  windowSize : ℕ
  curvatureBudget : ℕ
  remainderBudget : ℕ
deriving DecidableEq, Repr

def positiveWindow (d : UniformLaplaceData) : Prop :=
  0 < d.windowSize

def positiveCurvature (d : UniformLaplaceData) : Prop :=
  0 < d.curvatureBudget

def uniformLaplaceReady (d : UniformLaplaceData) : Prop :=
  positiveWindow d ∧ positiveCurvature d

def laplaceBudget (d : UniformLaplaceData) : ℕ :=
  d.windowSize * d.curvatureBudget + d.remainderBudget

theorem uniformLaplaceReady.curvature {d : UniformLaplaceData}
    (h : uniformLaplaceReady d) :
    positiveWindow d ∧ positiveCurvature d ∧ d.remainderBudget ≤ laplaceBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold laplaceBudget
  omega

theorem remainderBudget_le_laplaceBudget (d : UniformLaplaceData) :
    d.remainderBudget ≤ laplaceBudget d := by
  unfold laplaceBudget
  omega

def sampleUniformLaplace : UniformLaplaceData :=
  { windowSize := 4, curvatureBudget := 3, remainderBudget := 2 }

example : uniformLaplaceReady sampleUniformLaplace := by
  norm_num [uniformLaplaceReady, positiveWindow, positiveCurvature, sampleUniformLaplace]

example : laplaceBudget sampleUniformLaplace = 14 := by
  native_decide

/-- Finite executable readiness audit for uniform Laplace data. -/
def uniformLaplaceDataListReady (data : List UniformLaplaceData) : Bool :=
  data.all fun d => 0 < d.windowSize && 0 < d.curvatureBudget

theorem uniformLaplaceDataList_readyWindow :
    uniformLaplaceDataListReady
      [{ windowSize := 4, curvatureBudget := 3, remainderBudget := 2 },
       { windowSize := 5, curvatureBudget := 2, remainderBudget := 6 }] = true := by
  unfold uniformLaplaceDataListReady
  native_decide

structure UniformLaplaceWindow where
  windowSize : ℕ
  curvatureBudget : ℕ
  remainderBudget : ℕ
  amplitudeBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformLaplaceWindow.remainderControlled (w : UniformLaplaceWindow) : Prop :=
  w.remainderBudget ≤ w.windowSize * w.curvatureBudget + w.slack

def UniformLaplaceWindow.amplitudeControlled (w : UniformLaplaceWindow) : Prop :=
  w.amplitudeBudget ≤ w.windowSize * w.curvatureBudget + w.remainderBudget + w.slack

def uniformLaplaceWindowReady (w : UniformLaplaceWindow) : Prop :=
  0 < w.windowSize ∧
    0 < w.curvatureBudget ∧
    w.remainderControlled ∧
    w.amplitudeControlled

def UniformLaplaceWindow.certificate (w : UniformLaplaceWindow) : ℕ :=
  w.windowSize * w.curvatureBudget + w.remainderBudget + w.slack

theorem uniformLaplace_amplitudeBudget_le_certificate {w : UniformLaplaceWindow}
    (h : uniformLaplaceWindowReady w) :
    w.amplitudeBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hamp⟩
  exact hamp

def sampleUniformLaplaceWindow : UniformLaplaceWindow :=
  { windowSize := 4, curvatureBudget := 3, remainderBudget := 2, amplitudeBudget := 13,
    slack := 0 }

example : uniformLaplaceWindowReady sampleUniformLaplaceWindow := by
  norm_num [uniformLaplaceWindowReady, UniformLaplaceWindow.remainderControlled,
    UniformLaplaceWindow.amplitudeControlled, sampleUniformLaplaceWindow]

example : sampleUniformLaplaceWindow.certificate = 14 := by
  native_decide

structure UniformLaplaceCertificate where
  windowBudget : ℕ
  curvatureWindow : ℕ
  remainderWindow : ℕ
  amplitudeWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformLaplaceCertificate.remainderControlled
    (c : UniformLaplaceCertificate) : Prop :=
  c.remainderWindow ≤ c.windowBudget * c.curvatureWindow + c.slack

def UniformLaplaceCertificate.amplitudeControlled
    (c : UniformLaplaceCertificate) : Prop :=
  c.amplitudeWindow ≤
    c.windowBudget * c.curvatureWindow + c.remainderWindow + c.slack

def uniformLaplaceCertificateReady
    (c : UniformLaplaceCertificate) : Prop :=
  0 < c.windowBudget ∧
    0 < c.curvatureWindow ∧
    c.remainderControlled ∧
    c.amplitudeControlled

def UniformLaplaceCertificate.size
    (c : UniformLaplaceCertificate) : ℕ :=
  c.windowBudget * c.curvatureWindow + c.remainderWindow + c.slack

theorem uniformLaplace_amplitudeWindow_le_size
    {c : UniformLaplaceCertificate}
    (h : uniformLaplaceCertificateReady c) :
    c.amplitudeWindow ≤ c.size := by
  rcases h with ⟨_, _, _, hamplitude⟩
  exact hamplitude

def sampleUniformLaplaceCertificate : UniformLaplaceCertificate :=
  { windowBudget := 4, curvatureWindow := 3, remainderWindow := 2,
    amplitudeWindow := 13, slack := 0 }

example : uniformLaplaceCertificateReady sampleUniformLaplaceCertificate := by
  norm_num [uniformLaplaceCertificateReady,
    UniformLaplaceCertificate.remainderControlled,
    UniformLaplaceCertificate.amplitudeControlled,
    sampleUniformLaplaceCertificate]

example :
    sampleUniformLaplaceCertificate.amplitudeWindow ≤
      sampleUniformLaplaceCertificate.size := by
  norm_num [UniformLaplaceCertificate.size, sampleUniformLaplaceCertificate]

/-- A refinement certificate with the uniform-Laplace budget separated from size. -/
structure UniformLaplaceRefinementCertificate where
  windowBudget : ℕ
  curvatureWindow : ℕ
  remainderWindow : ℕ
  amplitudeWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformLaplaceRefinementCertificate.laplaceControlled
    (cert : UniformLaplaceRefinementCertificate) : Prop :=
  0 < cert.windowBudget ∧
    0 < cert.curvatureWindow ∧
      cert.remainderWindow ≤ cert.windowBudget * cert.curvatureWindow + cert.slack ∧
        cert.amplitudeWindow ≤
          cert.windowBudget * cert.curvatureWindow + cert.remainderWindow + cert.slack

def UniformLaplaceRefinementCertificate.budgetControlled
    (cert : UniformLaplaceRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.windowBudget * cert.curvatureWindow + cert.remainderWindow + cert.slack

def uniformLaplaceRefinementReady
    (cert : UniformLaplaceRefinementCertificate) : Prop :=
  cert.laplaceControlled ∧ cert.budgetControlled

def UniformLaplaceRefinementCertificate.size
    (cert : UniformLaplaceRefinementCertificate) : ℕ :=
  cert.windowBudget * cert.curvatureWindow + cert.remainderWindow + cert.slack

theorem uniformLaplace_certificateBudgetWindow_le_size
    (cert : UniformLaplaceRefinementCertificate)
    (h : uniformLaplaceRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformLaplaceRefinementCertificate :
    UniformLaplaceRefinementCertificate :=
  { windowBudget := 4, curvatureWindow := 3, remainderWindow := 2,
    amplitudeWindow := 13, certificateBudgetWindow := 14, slack := 0 }

example :
    uniformLaplaceRefinementReady sampleUniformLaplaceRefinementCertificate := by
  norm_num [uniformLaplaceRefinementReady,
    UniformLaplaceRefinementCertificate.laplaceControlled,
    UniformLaplaceRefinementCertificate.budgetControlled,
    sampleUniformLaplaceRefinementCertificate]

example :
    sampleUniformLaplaceRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformLaplaceRefinementCertificate.size := by
  apply uniformLaplace_certificateBudgetWindow_le_size
  norm_num [uniformLaplaceRefinementReady,
    UniformLaplaceRefinementCertificate.laplaceControlled,
    UniformLaplaceRefinementCertificate.budgetControlled,
    sampleUniformLaplaceRefinementCertificate]


structure UniformLaplaceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformLaplaceSchemasBudgetCertificate.controlled
    (c : UniformLaplaceSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def UniformLaplaceSchemasBudgetCertificate.budgetControlled
    (c : UniformLaplaceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformLaplaceSchemasBudgetCertificate.Ready
    (c : UniformLaplaceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformLaplaceSchemasBudgetCertificate.size
    (c : UniformLaplaceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformLaplaceSchemas_budgetCertificate_le_size
    (c : UniformLaplaceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformLaplaceSchemasBudgetCertificate :
    UniformLaplaceSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleUniformLaplaceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformLaplaceSchemasBudgetCertificate.controlled,
      sampleUniformLaplaceSchemasBudgetCertificate]
  · norm_num [UniformLaplaceSchemasBudgetCertificate.budgetControlled,
      sampleUniformLaplaceSchemasBudgetCertificate]

example :
    sampleUniformLaplaceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformLaplaceSchemasBudgetCertificate.size := by
  apply uniformLaplaceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [UniformLaplaceSchemasBudgetCertificate.controlled,
      sampleUniformLaplaceSchemasBudgetCertificate]
  · norm_num [UniformLaplaceSchemasBudgetCertificate.budgetControlled,
      sampleUniformLaplaceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformLaplaceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformLaplaceSchemasBudgetCertificate.controlled,
      sampleUniformLaplaceSchemasBudgetCertificate]
  · norm_num [UniformLaplaceSchemasBudgetCertificate.budgetControlled,
      sampleUniformLaplaceSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformLaplaceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformLaplaceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformLaplaceSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformLaplaceSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformLaplaceSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformLaplaceSchemas
