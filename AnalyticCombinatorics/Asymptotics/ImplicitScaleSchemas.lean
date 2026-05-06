import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Implicit scale schema bookkeeping.

The finite schema records equation rank, scale budget, and residual error
for implicitly defined asymptotic scales.
-/

namespace AnalyticCombinatorics.Asymptotics.ImplicitScaleSchemas

structure ImplicitScaleData where
  equationRank : ℕ
  scaleBudget : ℕ
  residualError : ℕ
deriving DecidableEq, Repr

def positiveEquationRank (d : ImplicitScaleData) : Prop :=
  0 < d.equationRank

def positiveScaleBudget (d : ImplicitScaleData) : Prop :=
  0 < d.scaleBudget

def implicitScaleReady (d : ImplicitScaleData) : Prop :=
  positiveEquationRank d ∧ positiveScaleBudget d

def implicitScaleComplexity (d : ImplicitScaleData) : ℕ :=
  d.equationRank * d.scaleBudget + d.residualError

theorem implicitScaleReady.scale {d : ImplicitScaleData}
    (h : implicitScaleReady d) :
    positiveEquationRank d ∧ positiveScaleBudget d ∧
      d.residualError ≤ implicitScaleComplexity d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold implicitScaleComplexity
  omega

theorem residualError_le_complexity (d : ImplicitScaleData) :
    d.residualError ≤ implicitScaleComplexity d := by
  unfold implicitScaleComplexity
  omega

def sampleImplicitScale : ImplicitScaleData :=
  { equationRank := 3, scaleBudget := 4, residualError := 2 }

example : implicitScaleReady sampleImplicitScale := by
  norm_num [implicitScaleReady, positiveEquationRank, positiveScaleBudget, sampleImplicitScale]

example : implicitScaleComplexity sampleImplicitScale = 14 := by
  native_decide

/-- Finite executable readiness audit for implicit scale data. -/
def implicitScaleDataListReady (data : List ImplicitScaleData) : Bool :=
  data.all fun d => 0 < d.equationRank && 0 < d.scaleBudget

theorem implicitScaleDataList_readyWindow :
    implicitScaleDataListReady
      [{ equationRank := 2, scaleBudget := 3, residualError := 1 },
       { equationRank := 3, scaleBudget := 4, residualError := 2 }] = true := by
  unfold implicitScaleDataListReady
  native_decide

structure ImplicitScaleWindow where
  equationRank : ℕ
  scaleBudget : ℕ
  residualError : ℕ
  iterationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitScaleWindow.residualControlled (w : ImplicitScaleWindow) : Prop :=
  w.residualError ≤ w.equationRank * w.scaleBudget + w.slack

def ImplicitScaleWindow.iterationControlled (w : ImplicitScaleWindow) : Prop :=
  w.iterationBudget ≤ w.equationRank * w.scaleBudget + w.residualError + w.slack

def implicitScaleWindowReady (w : ImplicitScaleWindow) : Prop :=
  0 < w.equationRank ∧
    0 < w.scaleBudget ∧
    w.residualControlled ∧
    w.iterationControlled

def ImplicitScaleWindow.certificate (w : ImplicitScaleWindow) : ℕ :=
  w.equationRank * w.scaleBudget + w.residualError + w.slack

theorem implicitScale_iterationBudget_le_certificate {w : ImplicitScaleWindow}
    (h : implicitScaleWindowReady w) :
    w.iterationBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hiteration⟩
  exact hiteration

def sampleImplicitScaleWindow : ImplicitScaleWindow :=
  { equationRank := 3, scaleBudget := 4, residualError := 2, iterationBudget := 13, slack := 0 }

example : implicitScaleWindowReady sampleImplicitScaleWindow := by
  norm_num [implicitScaleWindowReady, ImplicitScaleWindow.residualControlled,
    ImplicitScaleWindow.iterationControlled, sampleImplicitScaleWindow]

example : sampleImplicitScaleWindow.certificate = 14 := by
  native_decide

structure ImplicitScaleCertificate where
  rankWindow : ℕ
  scaleWindow : ℕ
  residualWindow : ℕ
  iterationWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitScaleCertificate.residualControlled
    (c : ImplicitScaleCertificate) : Prop :=
  c.residualWindow ≤ c.rankWindow * c.scaleWindow + c.slack

def ImplicitScaleCertificate.iterationControlled
    (c : ImplicitScaleCertificate) : Prop :=
  c.iterationWindow ≤ c.rankWindow * c.scaleWindow + c.residualWindow + c.slack

def implicitScaleCertificateReady
    (c : ImplicitScaleCertificate) : Prop :=
  0 < c.rankWindow ∧
    0 < c.scaleWindow ∧
    c.residualControlled ∧
    c.iterationControlled

def ImplicitScaleCertificate.size
    (c : ImplicitScaleCertificate) : ℕ :=
  c.rankWindow * c.scaleWindow + c.residualWindow + c.slack

theorem implicitScale_iterationWindow_le_size
    {c : ImplicitScaleCertificate}
    (h : implicitScaleCertificateReady c) :
    c.iterationWindow ≤ c.size := by
  rcases h with ⟨_, _, _, hiteration⟩
  exact hiteration

def sampleImplicitScaleCertificate : ImplicitScaleCertificate :=
  { rankWindow := 3, scaleWindow := 4, residualWindow := 2,
    iterationWindow := 13, slack := 0 }

example : implicitScaleCertificateReady sampleImplicitScaleCertificate := by
  norm_num [implicitScaleCertificateReady,
    ImplicitScaleCertificate.residualControlled,
    ImplicitScaleCertificate.iterationControlled,
    sampleImplicitScaleCertificate]

example :
    sampleImplicitScaleCertificate.iterationWindow ≤
      sampleImplicitScaleCertificate.size := by
  norm_num [ImplicitScaleCertificate.size, sampleImplicitScaleCertificate]

/-- A refinement certificate with the implicit-iteration budget separated from size. -/
structure ImplicitScaleRefinementCertificate where
  rankWindow : ℕ
  scaleWindow : ℕ
  residualWindow : ℕ
  iterationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitScaleRefinementCertificate.scaleControlled
    (cert : ImplicitScaleRefinementCertificate) : Prop :=
  0 < cert.rankWindow ∧
    0 < cert.scaleWindow ∧
      cert.residualWindow ≤ cert.rankWindow * cert.scaleWindow + cert.slack ∧
        cert.iterationWindow ≤
          cert.rankWindow * cert.scaleWindow + cert.residualWindow + cert.slack

def ImplicitScaleRefinementCertificate.budgetControlled
    (cert : ImplicitScaleRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.rankWindow * cert.scaleWindow + cert.residualWindow + cert.slack

def implicitScaleRefinementReady
    (cert : ImplicitScaleRefinementCertificate) : Prop :=
  cert.scaleControlled ∧ cert.budgetControlled

def ImplicitScaleRefinementCertificate.size
    (cert : ImplicitScaleRefinementCertificate) : ℕ :=
  cert.rankWindow * cert.scaleWindow + cert.residualWindow + cert.slack

theorem implicitScale_certificateBudgetWindow_le_size
    (cert : ImplicitScaleRefinementCertificate)
    (h : implicitScaleRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleImplicitScaleRefinementCertificate :
    ImplicitScaleRefinementCertificate :=
  { rankWindow := 3, scaleWindow := 4, residualWindow := 2,
    iterationWindow := 13, certificateBudgetWindow := 14, slack := 0 }

example :
    implicitScaleRefinementReady sampleImplicitScaleRefinementCertificate := by
  norm_num [implicitScaleRefinementReady,
    ImplicitScaleRefinementCertificate.scaleControlled,
    ImplicitScaleRefinementCertificate.budgetControlled,
    sampleImplicitScaleRefinementCertificate]

example :
    sampleImplicitScaleRefinementCertificate.certificateBudgetWindow ≤
      sampleImplicitScaleRefinementCertificate.size := by
  apply implicitScale_certificateBudgetWindow_le_size
  norm_num [implicitScaleRefinementReady,
    ImplicitScaleRefinementCertificate.scaleControlled,
    ImplicitScaleRefinementCertificate.budgetControlled,
    sampleImplicitScaleRefinementCertificate]


structure ImplicitScaleSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitScaleSchemasBudgetCertificate.controlled
    (c : ImplicitScaleSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def ImplicitScaleSchemasBudgetCertificate.budgetControlled
    (c : ImplicitScaleSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ImplicitScaleSchemasBudgetCertificate.Ready
    (c : ImplicitScaleSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ImplicitScaleSchemasBudgetCertificate.size
    (c : ImplicitScaleSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem implicitScaleSchemas_budgetCertificate_le_size
    (c : ImplicitScaleSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleImplicitScaleSchemasBudgetCertificate :
    ImplicitScaleSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleImplicitScaleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ImplicitScaleSchemasBudgetCertificate.controlled,
      sampleImplicitScaleSchemasBudgetCertificate]
  · norm_num [ImplicitScaleSchemasBudgetCertificate.budgetControlled,
      sampleImplicitScaleSchemasBudgetCertificate]

example :
    sampleImplicitScaleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitScaleSchemasBudgetCertificate.size := by
  apply implicitScaleSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ImplicitScaleSchemasBudgetCertificate.controlled,
      sampleImplicitScaleSchemasBudgetCertificate]
  · norm_num [ImplicitScaleSchemasBudgetCertificate.budgetControlled,
      sampleImplicitScaleSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleImplicitScaleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ImplicitScaleSchemasBudgetCertificate.controlled,
      sampleImplicitScaleSchemasBudgetCertificate]
  · norm_num [ImplicitScaleSchemasBudgetCertificate.budgetControlled,
      sampleImplicitScaleSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleImplicitScaleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitScaleSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ImplicitScaleSchemasBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleImplicitScaleSchemasBudgetCertificate] =
      true := by
  unfold budgetCertificateListReady sampleImplicitScaleSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.ImplicitScaleSchemas
