import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Critical composition schemas for implicit functional equations.

The file isolates the finite checks used when a composition schema reaches
its square-root critical point.
-/

namespace AnalyticCombinatorics.PartB.Ch7.CriticalCompositionSchemas

structure CriticalCompositionData where
  criticalRank : ℕ
  period : ℕ
  varianceScale : ℕ
deriving DecidableEq, Repr

def aperiodic (d : CriticalCompositionData) : Prop :=
  d.period = 1

def criticalNondegenerate (d : CriticalCompositionData) : Prop :=
  0 < d.criticalRank ∧ 0 < d.varianceScale

def compositionReady (d : CriticalCompositionData) : Prop :=
  aperiodic d ∧ criticalNondegenerate d

def criticalSize (rank offset n : ℕ) : ℕ :=
  rank * n + offset

theorem compositionReady.rank_pos {d : CriticalCompositionData}
    (h : compositionReady d) :
    0 < d.criticalRank := h.2.1

theorem criticalSize_succ (rank offset n : ℕ) :
    criticalSize rank offset (n + 1) =
      criticalSize rank offset n + rank := by
  unfold criticalSize
  rw [Nat.mul_succ]
  omega

def sampleCritical : CriticalCompositionData :=
  { criticalRank := 2, period := 1, varianceScale := 7 }

example : compositionReady sampleCritical := by
  norm_num [compositionReady, aperiodic, criticalNondegenerate, sampleCritical]

example : criticalSize 2 3 6 = 15 := by
  native_decide

structure CriticalCompositionWindow where
  criticalRank : ℕ
  period : ℕ
  varianceScale : ℕ
  compositionMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CriticalCompositionWindow.massControlled (w : CriticalCompositionWindow) : Prop :=
  w.compositionMass ≤ w.criticalRank * w.varianceScale + w.slack

def criticalCompositionWindowReady (w : CriticalCompositionWindow) : Prop :=
  w.period = 1 ∧
    0 < w.criticalRank ∧
    0 < w.varianceScale ∧
    w.massControlled

def CriticalCompositionWindow.certificate (w : CriticalCompositionWindow) : ℕ :=
  w.criticalRank * w.varianceScale + w.slack

theorem criticalComposition_mass_le_certificate {w : CriticalCompositionWindow}
    (h : criticalCompositionWindowReady w) :
    w.compositionMass ≤ w.certificate := by
  rcases h with ⟨_, _, _, hmass⟩
  exact hmass

def sampleCriticalCompositionWindow : CriticalCompositionWindow :=
  { criticalRank := 2, period := 1, varianceScale := 7, compositionMass := 12, slack := 0 }

example : criticalCompositionWindowReady sampleCriticalCompositionWindow := by
  norm_num [criticalCompositionWindowReady, CriticalCompositionWindow.massControlled,
    sampleCriticalCompositionWindow]

example : sampleCriticalCompositionWindow.certificate = 14 := by
  native_decide


structure CriticalCompositionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CriticalCompositionSchemasBudgetCertificate.controlled
    (c : CriticalCompositionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CriticalCompositionSchemasBudgetCertificate.budgetControlled
    (c : CriticalCompositionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CriticalCompositionSchemasBudgetCertificate.Ready
    (c : CriticalCompositionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CriticalCompositionSchemasBudgetCertificate.size
    (c : CriticalCompositionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem criticalCompositionSchemas_budgetCertificate_le_size
    (c : CriticalCompositionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCriticalCompositionSchemasBudgetCertificate :
    CriticalCompositionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCriticalCompositionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CriticalCompositionSchemasBudgetCertificate.controlled,
      sampleCriticalCompositionSchemasBudgetCertificate]
  · norm_num [CriticalCompositionSchemasBudgetCertificate.budgetControlled,
      sampleCriticalCompositionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCriticalCompositionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalCompositionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCriticalCompositionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CriticalCompositionSchemasBudgetCertificate.controlled,
      sampleCriticalCompositionSchemasBudgetCertificate]
  · norm_num [CriticalCompositionSchemasBudgetCertificate.budgetControlled,
      sampleCriticalCompositionSchemasBudgetCertificate]

example :
    sampleCriticalCompositionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalCompositionSchemasBudgetCertificate.size := by
  apply criticalCompositionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CriticalCompositionSchemasBudgetCertificate.controlled,
      sampleCriticalCompositionSchemasBudgetCertificate]
  · norm_num [CriticalCompositionSchemasBudgetCertificate.budgetControlled,
      sampleCriticalCompositionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CriticalCompositionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCriticalCompositionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCriticalCompositionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.CriticalCompositionSchemas
