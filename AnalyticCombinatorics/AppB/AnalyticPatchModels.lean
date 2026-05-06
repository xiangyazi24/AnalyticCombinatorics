import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic patch bookkeeping.

The finite schema records chart count, overlap budget, and gluing error for
patching local analytic data.
-/

namespace AnalyticCombinatorics.AppB.AnalyticPatchModels

structure PatchDatum where
  chartCount : ℕ
  overlapBudget : ℕ
  gluingError : ℕ
deriving DecidableEq, Repr

def nonemptyPatchCover (d : PatchDatum) : Prop :=
  0 < d.chartCount

def gluingErrorControlled (d : PatchDatum) : Prop :=
  d.gluingError ≤ d.chartCount + d.overlapBudget

def patchReady (d : PatchDatum) : Prop :=
  nonemptyPatchCover d ∧ gluingErrorControlled d

def patchComplexity (d : PatchDatum) : ℕ :=
  d.chartCount + d.overlapBudget + d.gluingError

theorem patchReady.cover {d : PatchDatum}
    (h : patchReady d) :
    nonemptyPatchCover d ∧ gluingErrorControlled d ∧
      d.chartCount ≤ patchComplexity d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold patchComplexity
  omega

theorem chartCount_le_patchComplexity (d : PatchDatum) :
    d.chartCount ≤ patchComplexity d := by
  unfold patchComplexity
  omega

def samplePatch : PatchDatum :=
  { chartCount := 4, overlapBudget := 6, gluingError := 3 }

example : patchReady samplePatch := by
  norm_num [patchReady, nonemptyPatchCover, gluingErrorControlled, samplePatch]

example : patchComplexity samplePatch = 13 := by
  native_decide

structure PatchWindow where
  chartWindow : ℕ
  overlapWindow : ℕ
  gluingWindow : ℕ
  patchBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PatchWindow.gluingControlled (w : PatchWindow) : Prop :=
  w.gluingWindow ≤ w.chartWindow + w.overlapWindow + w.slack

def patchWindowReady (w : PatchWindow) : Prop :=
  0 < w.chartWindow ∧ w.gluingControlled ∧
    w.patchBudget ≤ w.chartWindow + w.overlapWindow + w.gluingWindow + w.slack

def PatchWindow.certificate (w : PatchWindow) : ℕ :=
  w.chartWindow + w.overlapWindow + w.gluingWindow + w.patchBudget + w.slack

theorem patch_patchBudget_le_certificate (w : PatchWindow) :
    w.patchBudget ≤ w.certificate := by
  unfold PatchWindow.certificate
  omega

def samplePatchWindow : PatchWindow :=
  { chartWindow := 4, overlapWindow := 5, gluingWindow := 3, patchBudget := 13, slack := 2 }

example : patchWindowReady samplePatchWindow := by
  norm_num [patchWindowReady, PatchWindow.gluingControlled, samplePatchWindow]


structure AnalyticPatchModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticPatchModelsBudgetCertificate.controlled
    (c : AnalyticPatchModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticPatchModelsBudgetCertificate.budgetControlled
    (c : AnalyticPatchModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticPatchModelsBudgetCertificate.Ready
    (c : AnalyticPatchModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticPatchModelsBudgetCertificate.size
    (c : AnalyticPatchModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticPatchModels_budgetCertificate_le_size
    (c : AnalyticPatchModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticPatchModelsBudgetCertificate :
    AnalyticPatchModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticPatchModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticPatchModelsBudgetCertificate.controlled,
      sampleAnalyticPatchModelsBudgetCertificate]
  · norm_num [AnalyticPatchModelsBudgetCertificate.budgetControlled,
      sampleAnalyticPatchModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticPatchModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticPatchModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticPatchModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticPatchModelsBudgetCertificate.controlled,
      sampleAnalyticPatchModelsBudgetCertificate]
  · norm_num [AnalyticPatchModelsBudgetCertificate.budgetControlled,
      sampleAnalyticPatchModelsBudgetCertificate]

example :
    sampleAnalyticPatchModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticPatchModelsBudgetCertificate.size := by
  apply analyticPatchModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticPatchModelsBudgetCertificate.controlled,
      sampleAnalyticPatchModelsBudgetCertificate]
  · norm_num [AnalyticPatchModelsBudgetCertificate.budgetControlled,
      sampleAnalyticPatchModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticPatchModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticPatchModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticPatchModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticPatchModels
