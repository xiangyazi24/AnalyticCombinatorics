import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform local-limit schema bookkeeping.

The finite data records variance lower bounds, lattice span, and uniform
error budgets.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformLocalLimitSchemas

structure UniformLocalLimitData where
  varianceLowerBound : ℕ
  latticeSpan : ℕ
  uniformError : ℕ
deriving DecidableEq, Repr

def positiveVarianceLowerBound (d : UniformLocalLimitData) : Prop :=
  0 < d.varianceLowerBound

def unitLatticeSpan (d : UniformLocalLimitData) : Prop :=
  d.latticeSpan = 1

def uniformLocalLimitReady (d : UniformLocalLimitData) : Prop :=
  positiveVarianceLowerBound d ∧ unitLatticeSpan d

def localLimitBudget (d : UniformLocalLimitData) : ℕ :=
  d.varianceLowerBound + d.uniformError

theorem uniformLocalLimitReady.variance {d : UniformLocalLimitData}
    (h : uniformLocalLimitReady d) :
    positiveVarianceLowerBound d ∧ unitLatticeSpan d ∧
      d.varianceLowerBound ≤ localLimitBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold localLimitBudget
  omega

theorem varianceLowerBound_le_budget (d : UniformLocalLimitData) :
    d.varianceLowerBound ≤ localLimitBudget d := by
  unfold localLimitBudget
  omega

def sampleUniformLocalLimit : UniformLocalLimitData :=
  { varianceLowerBound := 4, latticeSpan := 1, uniformError := 3 }

example : uniformLocalLimitReady sampleUniformLocalLimit := by
  norm_num
    [uniformLocalLimitReady, positiveVarianceLowerBound, unitLatticeSpan,
      sampleUniformLocalLimit]

example : localLimitBudget sampleUniformLocalLimit = 7 := by
  native_decide

/-- Finite executable readiness audit for uniform local-limit data. -/
def uniformLocalLimitDataListReady
    (data : List UniformLocalLimitData) : Bool :=
  data.all fun d => 0 < d.varianceLowerBound && d.latticeSpan == 1

theorem uniformLocalLimitDataList_readyWindow :
    uniformLocalLimitDataListReady
      [{ varianceLowerBound := 4, latticeSpan := 1, uniformError := 3 },
       { varianceLowerBound := 6, latticeSpan := 1, uniformError := 2 }] = true := by
  unfold uniformLocalLimitDataListReady
  native_decide

/-- A certificate window for uniform local-limit schemas. -/
structure UniformLocalLimitCertificateWindow where
  varianceWindow : ℕ
  latticeWindow : ℕ
  errorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The lattice window is fixed to one and variance is positive. -/
def uniformLocalLimitCertificateControlled
    (w : UniformLocalLimitCertificateWindow) : Prop :=
  w.latticeWindow = 1 ∧ 0 < w.varianceWindow

/-- Readiness for a uniform local-limit certificate. -/
def uniformLocalLimitCertificateReady
    (w : UniformLocalLimitCertificateWindow) : Prop :=
  uniformLocalLimitCertificateControlled w ∧
    w.certificateBudget ≤ w.varianceWindow + w.errorWindow + w.slack

/-- Total size of a uniform local-limit certificate. -/
def uniformLocalLimitCertificate
    (w : UniformLocalLimitCertificateWindow) : ℕ :=
  w.varianceWindow + w.latticeWindow + w.errorWindow +
    w.certificateBudget + w.slack

theorem uniformLocalLimitCertificate_budget_le_certificate
    (w : UniformLocalLimitCertificateWindow)
    (h : uniformLocalLimitCertificateReady w) :
    w.certificateBudget ≤ uniformLocalLimitCertificate w := by
  rcases h with ⟨_, hbudget⟩
  unfold uniformLocalLimitCertificate
  omega

def sampleUniformLocalLimitCertificateWindow :
    UniformLocalLimitCertificateWindow where
  varianceWindow := 4
  latticeWindow := 1
  errorWindow := 3
  certificateBudget := 7
  slack := 1

example :
    uniformLocalLimitCertificateReady
      sampleUniformLocalLimitCertificateWindow := by
  norm_num [uniformLocalLimitCertificateReady,
    uniformLocalLimitCertificateControlled,
    sampleUniformLocalLimitCertificateWindow]

example :
    sampleUniformLocalLimitCertificateWindow.certificateBudget ≤
      uniformLocalLimitCertificate
        sampleUniformLocalLimitCertificateWindow := by
  apply uniformLocalLimitCertificate_budget_le_certificate
  norm_num [uniformLocalLimitCertificateReady,
    uniformLocalLimitCertificateControlled,
    sampleUniformLocalLimitCertificateWindow]

structure UniformLocalLimitRefinementCertificate where
  varianceWindow : ℕ
  latticeWindow : ℕ
  errorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformLocalLimitRefinementCertificate.latticeControlled
    (c : UniformLocalLimitRefinementCertificate) : Prop :=
  c.latticeWindow = 1 ∧ 0 < c.varianceWindow

def UniformLocalLimitRefinementCertificate.certificateBudgetControlled
    (c : UniformLocalLimitRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.varianceWindow + c.latticeWindow + c.errorWindow + c.slack

def uniformLocalLimitRefinementReady
    (c : UniformLocalLimitRefinementCertificate) : Prop :=
  c.latticeControlled ∧ c.certificateBudgetControlled

def UniformLocalLimitRefinementCertificate.size
    (c : UniformLocalLimitRefinementCertificate) : ℕ :=
  c.varianceWindow + c.latticeWindow + c.errorWindow + c.slack

theorem uniformLocalLimit_certificateBudgetWindow_le_size
    {c : UniformLocalLimitRefinementCertificate}
    (h : uniformLocalLimitRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformLocalLimitRefinementCertificate :
    UniformLocalLimitRefinementCertificate :=
  { varianceWindow := 4, latticeWindow := 1, errorWindow := 3,
    certificateBudgetWindow := 9, slack := 1 }

example : uniformLocalLimitRefinementReady
    sampleUniformLocalLimitRefinementCertificate := by
  norm_num [uniformLocalLimitRefinementReady,
    UniformLocalLimitRefinementCertificate.latticeControlled,
    UniformLocalLimitRefinementCertificate.certificateBudgetControlled,
    sampleUniformLocalLimitRefinementCertificate]

example :
    sampleUniformLocalLimitRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformLocalLimitRefinementCertificate.size := by
  norm_num [UniformLocalLimitRefinementCertificate.size,
    sampleUniformLocalLimitRefinementCertificate]

structure UniformLocalLimitBudgetCertificate where
  varianceWindow : ℕ
  latticeWindow : ℕ
  errorWindow : ℕ
  localBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformLocalLimitBudgetCertificate.controlled
    (c : UniformLocalLimitBudgetCertificate) : Prop :=
  c.latticeWindow = 1 ∧
    0 < c.varianceWindow ∧
      c.localBudgetWindow ≤
        c.varianceWindow + c.latticeWindow + c.errorWindow + c.slack

def UniformLocalLimitBudgetCertificate.budgetControlled
    (c : UniformLocalLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.varianceWindow + c.latticeWindow + c.errorWindow +
      c.localBudgetWindow + c.slack

def UniformLocalLimitBudgetCertificate.Ready
    (c : UniformLocalLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformLocalLimitBudgetCertificate.size
    (c : UniformLocalLimitBudgetCertificate) : ℕ :=
  c.varianceWindow + c.latticeWindow + c.errorWindow +
    c.localBudgetWindow + c.slack

theorem uniformLocalLimit_budgetCertificate_le_size
    (c : UniformLocalLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformLocalLimitBudgetCertificate :
    UniformLocalLimitBudgetCertificate :=
  { varianceWindow := 4
    latticeWindow := 1
    errorWindow := 3
    localBudgetWindow := 9
    certificateBudgetWindow := 18
    slack := 1 }

example : sampleUniformLocalLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformLocalLimitBudgetCertificate.controlled,
      sampleUniformLocalLimitBudgetCertificate]
  · norm_num [UniformLocalLimitBudgetCertificate.budgetControlled,
      sampleUniformLocalLimitBudgetCertificate]

example :
    sampleUniformLocalLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformLocalLimitBudgetCertificate.size := by
  apply uniformLocalLimit_budgetCertificate_le_size
  constructor
  · norm_num [UniformLocalLimitBudgetCertificate.controlled,
      sampleUniformLocalLimitBudgetCertificate]
  · norm_num [UniformLocalLimitBudgetCertificate.budgetControlled,
      sampleUniformLocalLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformLocalLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformLocalLimitBudgetCertificate.controlled,
      sampleUniformLocalLimitBudgetCertificate]
  · norm_num [UniformLocalLimitBudgetCertificate.budgetControlled,
      sampleUniformLocalLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformLocalLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformLocalLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformLocalLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformLocalLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformLocalLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformLocalLimitSchemas
