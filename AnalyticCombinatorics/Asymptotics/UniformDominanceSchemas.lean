import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform dominance schema bookkeeping.

The module records finite majorant and minorant budgets for uniform
asymptotic estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformDominanceSchemas

structure DominanceData where
  minorant : ℕ
  target : ℕ
  majorant : ℕ
deriving DecidableEq, Repr

def dominanceBracket (d : DominanceData) : Prop :=
  d.minorant ≤ d.target ∧ d.target ≤ d.majorant

def dominanceWidth (d : DominanceData) : ℕ :=
  d.majorant - d.minorant

def uniformDominanceReady (d : DominanceData) : Prop :=
  dominanceBracket d

theorem dominanceBracket.minorant_le_majorant {d : DominanceData}
    (h : dominanceBracket d) :
    d.minorant ≤ d.majorant := le_trans h.1 h.2

theorem dominanceWidth_add {d : DominanceData}
    (h : dominanceBracket d) :
    dominanceWidth d + d.minorant = d.majorant := by
  unfold dominanceWidth
  exact Nat.sub_add_cancel (h.minorant_le_majorant)

def sampleDominance : DominanceData :=
  { minorant := 3, target := 6, majorant := 10 }

example : uniformDominanceReady sampleDominance := by
  norm_num [uniformDominanceReady, dominanceBracket, sampleDominance]

example : dominanceWidth sampleDominance = 7 := by
  native_decide

/-- Finite executable readiness audit for uniform dominance brackets. -/
def dominanceDataListReady (data : List DominanceData) : Bool :=
  data.all fun d => d.minorant ≤ d.target && d.target ≤ d.majorant

theorem dominanceDataList_readyWindow :
    dominanceDataListReady
      [{ minorant := 1, target := 2, majorant := 4 },
       { minorant := 3, target := 6, majorant := 10 }] = true := by
  unfold dominanceDataListReady
  native_decide

structure UniformDominanceWindow where
  parameterCount : ℕ
  minorantMass : ℕ
  targetMass : ℕ
  majorantMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformDominanceWindow.bracketReady (w : UniformDominanceWindow) : Prop :=
  w.minorantMass ≤ w.targetMass ∧ w.targetMass ≤ w.majorantMass + w.slack

def UniformDominanceWindow.parameterReady (w : UniformDominanceWindow) : Prop :=
  0 < w.parameterCount

def UniformDominanceWindow.ready (w : UniformDominanceWindow) : Prop :=
  w.parameterReady ∧ w.bracketReady

def UniformDominanceWindow.certificate (w : UniformDominanceWindow) : ℕ :=
  w.parameterCount + w.minorantMass + w.targetMass + w.majorantMass + w.slack

theorem targetMass_le_certificate (w : UniformDominanceWindow) :
    w.targetMass ≤ w.certificate := by
  unfold UniformDominanceWindow.certificate
  omega

def sampleUniformDominanceWindow : UniformDominanceWindow :=
  { parameterCount := 4, minorantMass := 3, targetMass := 6, majorantMass := 10, slack := 0 }

example : sampleUniformDominanceWindow.ready := by
  norm_num [sampleUniformDominanceWindow, UniformDominanceWindow.ready,
    UniformDominanceWindow.parameterReady, UniformDominanceWindow.bracketReady]

/-- A refinement certificate for uniform dominance windows. -/
structure UniformDominanceCertificate where
  parameterWindow : ℕ
  minorantWindow : ℕ
  targetWindow : ℕ
  majorantWindow : ℕ
  slack : ℕ

/-- The target lies between minorant and majorant windows up to slack. -/
def uniformDominanceCertificateControlled
    (w : UniformDominanceCertificate) : Prop :=
  0 < w.parameterWindow ∧
    w.minorantWindow ≤ w.targetWindow ∧
      w.targetWindow ≤ w.majorantWindow + w.slack

/-- Readiness for a uniform dominance certificate. -/
def uniformDominanceCertificateReady
    (w : UniformDominanceCertificate) : Prop :=
  uniformDominanceCertificateControlled w ∧
    w.targetWindow ≤
      w.parameterWindow + w.minorantWindow + w.targetWindow + w.majorantWindow + w.slack

/-- Total size of a uniform dominance certificate. -/
def uniformDominanceCertificateSize
    (w : UniformDominanceCertificate) : ℕ :=
  w.parameterWindow + w.minorantWindow + w.targetWindow +
    w.majorantWindow + w.slack

theorem uniformDominanceCertificate_target_le_size
    (w : UniformDominanceCertificate)
    (h : uniformDominanceCertificateReady w) :
    w.targetWindow ≤ uniformDominanceCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold uniformDominanceCertificateSize
  omega

def sampleUniformDominanceCertificate : UniformDominanceCertificate where
  parameterWindow := 4
  minorantWindow := 3
  targetWindow := 6
  majorantWindow := 10
  slack := 0

example :
    uniformDominanceCertificateReady sampleUniformDominanceCertificate := by
  norm_num [uniformDominanceCertificateReady,
    uniformDominanceCertificateControlled, sampleUniformDominanceCertificate]

example :
    sampleUniformDominanceCertificate.targetWindow ≤
      uniformDominanceCertificateSize sampleUniformDominanceCertificate := by
  apply uniformDominanceCertificate_target_le_size
  norm_num [uniformDominanceCertificateReady,
    uniformDominanceCertificateControlled, sampleUniformDominanceCertificate]

/-- A refinement certificate with the dominance budget separated from size. -/
structure UniformDominanceRefinementCertificate where
  parameterWindow : ℕ
  minorantWindow : ℕ
  targetWindow : ℕ
  majorantWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def UniformDominanceRefinementCertificate.bracketControlled
    (cert : UniformDominanceRefinementCertificate) : Prop :=
  0 < cert.parameterWindow ∧
    cert.minorantWindow ≤ cert.targetWindow ∧
      cert.targetWindow ≤ cert.majorantWindow + cert.slack

def UniformDominanceRefinementCertificate.budgetControlled
    (cert : UniformDominanceRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.parameterWindow + cert.minorantWindow + cert.targetWindow +
      cert.majorantWindow + cert.slack

def uniformDominanceRefinementReady
    (cert : UniformDominanceRefinementCertificate) : Prop :=
  cert.bracketControlled ∧ cert.budgetControlled

def UniformDominanceRefinementCertificate.size
    (cert : UniformDominanceRefinementCertificate) : ℕ :=
  cert.parameterWindow + cert.minorantWindow + cert.targetWindow +
    cert.majorantWindow + cert.slack

theorem uniformDominance_certificateBudgetWindow_le_size
    (cert : UniformDominanceRefinementCertificate)
    (h : uniformDominanceRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformDominanceRefinementCertificate :
    UniformDominanceRefinementCertificate where
  parameterWindow := 4
  minorantWindow := 3
  targetWindow := 6
  majorantWindow := 10
  certificateBudgetWindow := 23
  slack := 0

example :
    uniformDominanceRefinementReady sampleUniformDominanceRefinementCertificate := by
  norm_num [uniformDominanceRefinementReady,
    UniformDominanceRefinementCertificate.bracketControlled,
    UniformDominanceRefinementCertificate.budgetControlled,
    sampleUniformDominanceRefinementCertificate]

example :
    sampleUniformDominanceRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformDominanceRefinementCertificate.size := by
  apply uniformDominance_certificateBudgetWindow_le_size
  norm_num [uniformDominanceRefinementReady,
    UniformDominanceRefinementCertificate.bracketControlled,
    UniformDominanceRefinementCertificate.budgetControlled,
    sampleUniformDominanceRefinementCertificate]


structure UniformDominanceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformDominanceSchemasBudgetCertificate.controlled
    (c : UniformDominanceSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def UniformDominanceSchemasBudgetCertificate.budgetControlled
    (c : UniformDominanceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformDominanceSchemasBudgetCertificate.Ready
    (c : UniformDominanceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformDominanceSchemasBudgetCertificate.size
    (c : UniformDominanceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformDominanceSchemas_budgetCertificate_le_size
    (c : UniformDominanceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformDominanceSchemasBudgetCertificate :
    UniformDominanceSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleUniformDominanceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformDominanceSchemasBudgetCertificate.controlled,
      sampleUniformDominanceSchemasBudgetCertificate]
  · norm_num [UniformDominanceSchemasBudgetCertificate.budgetControlled,
      sampleUniformDominanceSchemasBudgetCertificate]

example :
    sampleUniformDominanceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformDominanceSchemasBudgetCertificate.size := by
  apply uniformDominanceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [UniformDominanceSchemasBudgetCertificate.controlled,
      sampleUniformDominanceSchemasBudgetCertificate]
  · norm_num [UniformDominanceSchemasBudgetCertificate.budgetControlled,
      sampleUniformDominanceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformDominanceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformDominanceSchemasBudgetCertificate.controlled,
      sampleUniformDominanceSchemasBudgetCertificate]
  · norm_num [UniformDominanceSchemasBudgetCertificate.budgetControlled,
      sampleUniformDominanceSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformDominanceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformDominanceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformDominanceSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformDominanceSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformDominanceSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformDominanceSchemas
