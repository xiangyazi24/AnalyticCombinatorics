import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Poisson saddle-point schemas.

The predicates below isolate the finite nondegeneracy and tail checks used
by Poissonized saddle-point estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.PoissonSaddleSchemas

structure PoissonSaddleData where
  saddleIndex : ℕ
  varianceScale : ℕ
  tailBudget : ℕ
deriving DecidableEq, Repr

def nondegenerate (d : PoissonSaddleData) : Prop :=
  0 < d.saddleIndex ∧ 0 < d.varianceScale

def tailControlled (d : PoissonSaddleData) : Prop :=
  d.tailBudget ≤ d.varianceScale

def saddleAdmissible (d : PoissonSaddleData) : Prop :=
  nondegenerate d ∧ tailControlled d

theorem saddleAdmissible_intro {d : PoissonSaddleData}
    (hn : nondegenerate d) (ht : tailControlled d) :
    saddleAdmissible d := by
  exact ⟨hn, ht⟩

theorem saddleAdmissible.tail {d : PoissonSaddleData}
    (h : saddleAdmissible d) :
    nondegenerate d ∧ tailControlled d ∧ d.tailBudget ≤ d.varianceScale := by
  exact ⟨h.1, h.2, h.2⟩

def sampleSaddle : PoissonSaddleData :=
  { saddleIndex := 6, varianceScale := 10, tailBudget := 4 }

example : nondegenerate sampleSaddle := by
  norm_num [nondegenerate, sampleSaddle]

example : tailControlled sampleSaddle := by
  norm_num [tailControlled, sampleSaddle]

example : saddleAdmissible sampleSaddle := by
  norm_num [saddleAdmissible, nondegenerate, tailControlled, sampleSaddle]

/-- Finite executable readiness audit for Poisson saddle data. -/
def poissonSaddleDataListReady (data : List PoissonSaddleData) : Bool :=
  data.all fun d =>
    0 < d.saddleIndex && 0 < d.varianceScale && d.tailBudget ≤ d.varianceScale

theorem poissonSaddleDataList_readyWindow :
    poissonSaddleDataListReady
      [{ saddleIndex := 3, varianceScale := 5, tailBudget := 2 },
       { saddleIndex := 6, varianceScale := 10, tailBudget := 4 }] = true := by
  unfold poissonSaddleDataListReady
  native_decide

structure PoissonSaddleWindow where
  saddleIndex : ℕ
  varianceScale : ℕ
  tailBudget : ℕ
  localMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonSaddleWindow.nonDegenerate (w : PoissonSaddleWindow) : Prop :=
  0 < w.saddleIndex ∧ 0 < w.varianceScale

def PoissonSaddleWindow.tailReady (w : PoissonSaddleWindow) : Prop :=
  w.tailBudget ≤ w.varianceScale + w.slack

def PoissonSaddleWindow.localControlled (w : PoissonSaddleWindow) : Prop :=
  w.localMass ≤ w.saddleIndex + w.varianceScale + w.slack

def PoissonSaddleWindow.ready (w : PoissonSaddleWindow) : Prop :=
  w.nonDegenerate ∧ w.tailReady ∧ w.localControlled

def PoissonSaddleWindow.certificate (w : PoissonSaddleWindow) : ℕ :=
  w.saddleIndex + w.varianceScale + w.tailBudget + w.localMass + w.slack

theorem localMass_le_certificate (w : PoissonSaddleWindow) :
    w.localMass ≤ w.certificate := by
  unfold PoissonSaddleWindow.certificate
  omega

def samplePoissonSaddleWindow : PoissonSaddleWindow :=
  { saddleIndex := 6, varianceScale := 10, tailBudget := 4, localMass := 12, slack := 0 }

example : samplePoissonSaddleWindow.ready := by
  norm_num [samplePoissonSaddleWindow, PoissonSaddleWindow.ready,
    PoissonSaddleWindow.nonDegenerate, PoissonSaddleWindow.tailReady,
    PoissonSaddleWindow.localControlled]

/-- A refinement certificate for Poisson saddle windows. -/
structure PoissonSaddleCertificate where
  saddleWindow : ℕ
  varianceWindow : ℕ
  tailWindow : ℕ
  localMassWindow : ℕ
  slack : ℕ

/-- Nondegeneracy controls tails and local mass. -/
def poissonSaddleCertificateControlled
    (w : PoissonSaddleCertificate) : Prop :=
  0 < w.saddleWindow ∧
    0 < w.varianceWindow ∧
      w.tailWindow ≤ w.varianceWindow + w.slack ∧
        w.localMassWindow ≤ w.saddleWindow + w.varianceWindow + w.slack

/-- Readiness for a Poisson saddle certificate. -/
def poissonSaddleCertificateReady
    (w : PoissonSaddleCertificate) : Prop :=
  poissonSaddleCertificateControlled w ∧
    w.localMassWindow ≤
      w.saddleWindow + w.varianceWindow + w.tailWindow + w.localMassWindow + w.slack

/-- Total size of a Poisson saddle certificate. -/
def poissonSaddleCertificateSize (w : PoissonSaddleCertificate) : ℕ :=
  w.saddleWindow + w.varianceWindow + w.tailWindow + w.localMassWindow + w.slack

theorem poissonSaddleCertificate_local_le_size
    (w : PoissonSaddleCertificate)
    (h : poissonSaddleCertificateReady w) :
    w.localMassWindow ≤ poissonSaddleCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold poissonSaddleCertificateSize
  omega

def samplePoissonSaddleCertificate : PoissonSaddleCertificate where
  saddleWindow := 6
  varianceWindow := 10
  tailWindow := 4
  localMassWindow := 12
  slack := 0

example :
    poissonSaddleCertificateReady samplePoissonSaddleCertificate := by
  norm_num [poissonSaddleCertificateReady,
    poissonSaddleCertificateControlled, samplePoissonSaddleCertificate]

example :
    samplePoissonSaddleCertificate.localMassWindow ≤
      poissonSaddleCertificateSize samplePoissonSaddleCertificate := by
  apply poissonSaddleCertificate_local_le_size
  norm_num [poissonSaddleCertificateReady,
    poissonSaddleCertificateControlled, samplePoissonSaddleCertificate]

/-- A refinement certificate with the Poisson local budget separated from size. -/
structure PoissonSaddleRefinementCertificate where
  saddleWindow : ℕ
  varianceWindow : ℕ
  tailWindow : ℕ
  localMassWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonSaddleRefinementCertificate.saddleControlled
    (cert : PoissonSaddleRefinementCertificate) : Prop :=
  0 < cert.saddleWindow ∧
    0 < cert.varianceWindow ∧
      cert.tailWindow ≤ cert.varianceWindow + cert.slack ∧
        cert.localMassWindow ≤ cert.saddleWindow + cert.varianceWindow + cert.slack

def PoissonSaddleRefinementCertificate.budgetControlled
    (cert : PoissonSaddleRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.saddleWindow + cert.varianceWindow + cert.tailWindow +
      cert.localMassWindow + cert.slack

def poissonSaddleRefinementReady
    (cert : PoissonSaddleRefinementCertificate) : Prop :=
  cert.saddleControlled ∧ cert.budgetControlled

def PoissonSaddleRefinementCertificate.size
    (cert : PoissonSaddleRefinementCertificate) : ℕ :=
  cert.saddleWindow + cert.varianceWindow + cert.tailWindow +
    cert.localMassWindow + cert.slack

theorem poissonSaddle_certificateBudgetWindow_le_size
    (cert : PoissonSaddleRefinementCertificate)
    (h : poissonSaddleRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePoissonSaddleRefinementCertificate :
    PoissonSaddleRefinementCertificate :=
  { saddleWindow := 6, varianceWindow := 10, tailWindow := 4,
    localMassWindow := 12, certificateBudgetWindow := 32, slack := 0 }

example :
    poissonSaddleRefinementReady samplePoissonSaddleRefinementCertificate := by
  norm_num [poissonSaddleRefinementReady,
    PoissonSaddleRefinementCertificate.saddleControlled,
    PoissonSaddleRefinementCertificate.budgetControlled,
    samplePoissonSaddleRefinementCertificate]

example :
    samplePoissonSaddleRefinementCertificate.certificateBudgetWindow ≤
      samplePoissonSaddleRefinementCertificate.size := by
  apply poissonSaddle_certificateBudgetWindow_le_size
  norm_num [poissonSaddleRefinementReady,
    PoissonSaddleRefinementCertificate.saddleControlled,
    PoissonSaddleRefinementCertificate.budgetControlled,
    samplePoissonSaddleRefinementCertificate]


structure PoissonSaddleSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonSaddleSchemasBudgetCertificate.controlled
    (c : PoissonSaddleSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def PoissonSaddleSchemasBudgetCertificate.budgetControlled
    (c : PoissonSaddleSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PoissonSaddleSchemasBudgetCertificate.Ready
    (c : PoissonSaddleSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PoissonSaddleSchemasBudgetCertificate.size
    (c : PoissonSaddleSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem poissonSaddleSchemas_budgetCertificate_le_size
    (c : PoissonSaddleSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePoissonSaddleSchemasBudgetCertificate :
    PoissonSaddleSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : samplePoissonSaddleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonSaddleSchemasBudgetCertificate.controlled,
      samplePoissonSaddleSchemasBudgetCertificate]
  · norm_num [PoissonSaddleSchemasBudgetCertificate.budgetControlled,
      samplePoissonSaddleSchemasBudgetCertificate]

example :
    samplePoissonSaddleSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonSaddleSchemasBudgetCertificate.size := by
  apply poissonSaddleSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PoissonSaddleSchemasBudgetCertificate.controlled,
      samplePoissonSaddleSchemasBudgetCertificate]
  · norm_num [PoissonSaddleSchemasBudgetCertificate.budgetControlled,
      samplePoissonSaddleSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePoissonSaddleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonSaddleSchemasBudgetCertificate.controlled,
      samplePoissonSaddleSchemasBudgetCertificate]
  · norm_num [PoissonSaddleSchemasBudgetCertificate.budgetControlled,
      samplePoissonSaddleSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePoissonSaddleSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonSaddleSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List PoissonSaddleSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePoissonSaddleSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    samplePoissonSaddleSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.PoissonSaddleSchemas
