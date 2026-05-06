import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform meromorphic patch models.

This module records finite bookkeeping for meromorphic patch covers.
-/

namespace AnalyticCombinatorics.AppB.UniformMeromorphicPatchModels

structure MeromorphicPatchData where
  patchCount : ℕ
  poleBudget : ℕ
  meromorphicSlack : ℕ
deriving DecidableEq, Repr

def hasPatchCount (d : MeromorphicPatchData) : Prop :=
  0 < d.patchCount

def poleBudgetControlled (d : MeromorphicPatchData) : Prop :=
  d.poleBudget ≤ d.patchCount + d.meromorphicSlack

def meromorphicPatchReady (d : MeromorphicPatchData) : Prop :=
  hasPatchCount d ∧ poleBudgetControlled d

def meromorphicPatchBudget (d : MeromorphicPatchData) : ℕ :=
  d.patchCount + d.poleBudget + d.meromorphicSlack

theorem meromorphicPatchReady.hasPatchCount {d : MeromorphicPatchData}
    (h : meromorphicPatchReady d) :
    hasPatchCount d ∧ poleBudgetControlled d ∧
      d.poleBudget ≤ meromorphicPatchBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold meromorphicPatchBudget
  omega

theorem poleBudget_le_budget (d : MeromorphicPatchData) :
    d.poleBudget ≤ meromorphicPatchBudget d := by
  unfold meromorphicPatchBudget
  omega

def sampleMeromorphicPatchData : MeromorphicPatchData :=
  { patchCount := 6, poleBudget := 8, meromorphicSlack := 3 }

example : meromorphicPatchReady sampleMeromorphicPatchData := by
  norm_num [meromorphicPatchReady, hasPatchCount]
  norm_num [poleBudgetControlled, sampleMeromorphicPatchData]

example : meromorphicPatchBudget sampleMeromorphicPatchData = 17 := by
  native_decide

structure UniformMeromorphicPatchWindow where
  patchWindow : ℕ
  poleWindow : ℕ
  meromorphicSlack : ℕ
  patchBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformMeromorphicPatchWindow.polesControlled
    (w : UniformMeromorphicPatchWindow) : Prop :=
  w.poleWindow ≤ w.patchWindow + w.meromorphicSlack + w.slack

def uniformMeromorphicPatchWindowReady (w : UniformMeromorphicPatchWindow) : Prop :=
  0 < w.patchWindow ∧ w.polesControlled ∧
    w.patchBudget ≤ w.patchWindow + w.poleWindow + w.slack

def UniformMeromorphicPatchWindow.certificate (w : UniformMeromorphicPatchWindow) : ℕ :=
  w.patchWindow + w.poleWindow + w.meromorphicSlack + w.patchBudget + w.slack

theorem uniformMeromorphicPatch_patchBudget_le_certificate
    (w : UniformMeromorphicPatchWindow) :
    w.patchBudget ≤ w.certificate := by
  unfold UniformMeromorphicPatchWindow.certificate
  omega

def sampleUniformMeromorphicPatchWindow : UniformMeromorphicPatchWindow :=
  { patchWindow := 5, poleWindow := 7, meromorphicSlack := 2, patchBudget := 14, slack := 2 }

example : uniformMeromorphicPatchWindowReady sampleUniformMeromorphicPatchWindow := by
  norm_num [uniformMeromorphicPatchWindowReady,
    UniformMeromorphicPatchWindow.polesControlled, sampleUniformMeromorphicPatchWindow]


structure UniformMeromorphicPatchModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformMeromorphicPatchModelsBudgetCertificate.controlled
    (c : UniformMeromorphicPatchModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformMeromorphicPatchModelsBudgetCertificate.budgetControlled
    (c : UniformMeromorphicPatchModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformMeromorphicPatchModelsBudgetCertificate.Ready
    (c : UniformMeromorphicPatchModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformMeromorphicPatchModelsBudgetCertificate.size
    (c : UniformMeromorphicPatchModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformMeromorphicPatchModels_budgetCertificate_le_size
    (c : UniformMeromorphicPatchModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformMeromorphicPatchModelsBudgetCertificate :
    UniformMeromorphicPatchModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformMeromorphicPatchModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformMeromorphicPatchModelsBudgetCertificate.controlled,
      sampleUniformMeromorphicPatchModelsBudgetCertificate]
  · norm_num [UniformMeromorphicPatchModelsBudgetCertificate.budgetControlled,
      sampleUniformMeromorphicPatchModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformMeromorphicPatchModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformMeromorphicPatchModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformMeromorphicPatchModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformMeromorphicPatchModelsBudgetCertificate.controlled,
      sampleUniformMeromorphicPatchModelsBudgetCertificate]
  · norm_num [UniformMeromorphicPatchModelsBudgetCertificate.budgetControlled,
      sampleUniformMeromorphicPatchModelsBudgetCertificate]

example :
    sampleUniformMeromorphicPatchModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformMeromorphicPatchModelsBudgetCertificate.size := by
  apply uniformMeromorphicPatchModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformMeromorphicPatchModelsBudgetCertificate.controlled,
      sampleUniformMeromorphicPatchModelsBudgetCertificate]
  · norm_num [UniformMeromorphicPatchModelsBudgetCertificate.budgetControlled,
      sampleUniformMeromorphicPatchModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformMeromorphicPatchModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformMeromorphicPatchModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformMeromorphicPatchModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformMeromorphicPatchModels
