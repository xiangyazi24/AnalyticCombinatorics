import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform boundedness bookkeeping.

The file records finite family size, pointwise bound, and common bound
budgets.
-/

namespace AnalyticCombinatorics.AppB.UniformBoundednessModels

structure UniformBoundDatum where
  familySize : ℕ
  pointwiseBound : ℕ
  uniformBound : ℕ
deriving DecidableEq, Repr

def nonemptyFamily (d : UniformBoundDatum) : Prop :=
  0 < d.familySize

def pointwiseLeUniform (d : UniformBoundDatum) : Prop :=
  d.pointwiseBound ≤ d.uniformBound

def uniformBoundReady (d : UniformBoundDatum) : Prop :=
  nonemptyFamily d ∧ pointwiseLeUniform d

def uniformSlack (d : UniformBoundDatum) : ℕ :=
  d.uniformBound - d.pointwiseBound

theorem uniformBoundReady.bound {d : UniformBoundDatum}
    (h : uniformBoundReady d) :
    nonemptyFamily d ∧ pointwiseLeUniform d := by
  refine ⟨h.1, h.2⟩

theorem uniformSlack_add {d : UniformBoundDatum}
    (h : pointwiseLeUniform d) :
    uniformSlack d + d.pointwiseBound = d.uniformBound := by
  unfold uniformSlack pointwiseLeUniform at *
  omega

def sampleUniformBound : UniformBoundDatum :=
  { familySize := 4, pointwiseBound := 7, uniformBound := 10 }

example : uniformBoundReady sampleUniformBound := by
  norm_num [uniformBoundReady, nonemptyFamily, pointwiseLeUniform, sampleUniformBound]

example : uniformSlack sampleUniformBound = 3 := by
  native_decide

structure UniformBoundWindow where
  familySize : ℕ
  pointwiseBound : ℕ
  uniformBound : ℕ
  compactnessBudget : ℕ
deriving DecidableEq, Repr

def UniformBoundWindow.familyReady (w : UniformBoundWindow) : Prop :=
  0 < w.familySize

def UniformBoundWindow.boundControlled (w : UniformBoundWindow) : Prop :=
  w.pointwiseBound ≤ w.uniformBound

def UniformBoundWindow.compactnessControlled (w : UniformBoundWindow) : Prop :=
  w.compactnessBudget ≤ w.familySize + w.uniformBound

def UniformBoundWindow.ready (w : UniformBoundWindow) : Prop :=
  w.familyReady ∧ w.boundControlled ∧ w.compactnessControlled

def UniformBoundWindow.certificate (w : UniformBoundWindow) : ℕ :=
  w.familySize + w.pointwiseBound + w.uniformBound + w.compactnessBudget

theorem compactnessBudget_le_certificate (w : UniformBoundWindow) :
    w.compactnessBudget ≤ w.certificate := by
  unfold UniformBoundWindow.certificate
  omega

def sampleUniformBoundWindow : UniformBoundWindow :=
  { familySize := 4, pointwiseBound := 7, uniformBound := 10, compactnessBudget := 8 }

example : sampleUniformBoundWindow.ready := by
  norm_num [sampleUniformBoundWindow, UniformBoundWindow.ready,
    UniformBoundWindow.familyReady, UniformBoundWindow.boundControlled,
    UniformBoundWindow.compactnessControlled]


structure UniformBoundednessModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformBoundednessModelsBudgetCertificate.controlled
    (c : UniformBoundednessModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformBoundednessModelsBudgetCertificate.budgetControlled
    (c : UniformBoundednessModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformBoundednessModelsBudgetCertificate.Ready
    (c : UniformBoundednessModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformBoundednessModelsBudgetCertificate.size
    (c : UniformBoundednessModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformBoundednessModels_budgetCertificate_le_size
    (c : UniformBoundednessModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformBoundednessModelsBudgetCertificate :
    UniformBoundednessModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformBoundednessModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformBoundednessModelsBudgetCertificate.controlled,
      sampleUniformBoundednessModelsBudgetCertificate]
  · norm_num [UniformBoundednessModelsBudgetCertificate.budgetControlled,
      sampleUniformBoundednessModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformBoundednessModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformBoundednessModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformBoundednessModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformBoundednessModelsBudgetCertificate.controlled,
      sampleUniformBoundednessModelsBudgetCertificate]
  · norm_num [UniformBoundednessModelsBudgetCertificate.budgetControlled,
      sampleUniformBoundednessModelsBudgetCertificate]

example :
    sampleUniformBoundednessModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformBoundednessModelsBudgetCertificate.size := by
  apply uniformBoundednessModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformBoundednessModelsBudgetCertificate.controlled,
      sampleUniformBoundednessModelsBudgetCertificate]
  · norm_num [UniformBoundednessModelsBudgetCertificate.budgetControlled,
      sampleUniformBoundednessModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformBoundednessModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformBoundednessModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformBoundednessModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformBoundednessModels
