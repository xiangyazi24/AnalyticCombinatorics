import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Moment bookkeeping schemas.
-/

namespace AnalyticCombinatorics.PartA.Ch3.Moments

structure MomentData where
  sampleCount : ℕ
  firstMoment : ℕ
  secondMoment : ℕ
deriving DecidableEq, Repr

def momentsReady (d : MomentData) : Prop :=
  0 < d.sampleCount ∧ d.firstMoment ≤ d.secondMoment + d.sampleCount

def momentBudget (d : MomentData) : ℕ :=
  d.sampleCount + d.firstMoment + d.secondMoment

theorem firstMoment_le_budget (d : MomentData) :
    d.firstMoment ≤ momentBudget d := by
  unfold momentBudget
  omega

def sampleMomentData : MomentData :=
  { sampleCount := 6, firstMoment := 9, secondMoment := 5 }

example : momentsReady sampleMomentData := by
  norm_num [momentsReady, sampleMomentData]

example : momentBudget sampleMomentData = 20 := by
  native_decide

structure MomentWindow where
  order : ℕ
  rawMoment : ℕ
  centeredMoment : ℕ
  normalization : ℕ
deriving DecidableEq, Repr

def MomentWindow.normalizedBound (w : MomentWindow) : ℕ :=
  w.centeredMoment + w.normalization

def MomentWindow.ready (w : MomentWindow) : Prop :=
  0 < w.order ∧ w.rawMoment ≤ w.normalizedBound

def MomentWindow.cumulantBudget (w : MomentWindow) : ℕ :=
  w.order * w.normalizedBound

def MomentWindow.certificate (w : MomentWindow) : ℕ :=
  w.order + w.rawMoment + w.centeredMoment + w.normalization

theorem rawMoment_le_certificate (w : MomentWindow) :
    w.rawMoment ≤ w.certificate := by
  unfold MomentWindow.certificate
  omega

def sampleMomentWindow : MomentWindow :=
  { order := 3, rawMoment := 14, centeredMoment := 9, normalization := 6 }

example : sampleMomentWindow.ready := by
  norm_num [sampleMomentWindow, MomentWindow.ready, MomentWindow.normalizedBound]

example : sampleMomentWindow.cumulantBudget = 45 := by
  norm_num [sampleMomentWindow, MomentWindow.cumulantBudget, MomentWindow.normalizedBound]


structure MomentsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MomentsBudgetCertificate.controlled
    (c : MomentsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MomentsBudgetCertificate.budgetControlled
    (c : MomentsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MomentsBudgetCertificate.Ready
    (c : MomentsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MomentsBudgetCertificate.size
    (c : MomentsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem moments_budgetCertificate_le_size
    (c : MomentsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMomentsBudgetCertificate :
    MomentsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMomentsBudgetCertificate.Ready := by
  constructor
  · norm_num [MomentsBudgetCertificate.controlled,
      sampleMomentsBudgetCertificate]
  · norm_num [MomentsBudgetCertificate.budgetControlled,
      sampleMomentsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMomentsBudgetCertificate.certificateBudgetWindow ≤
      sampleMomentsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMomentsBudgetCertificate.Ready := by
  constructor
  · norm_num [MomentsBudgetCertificate.controlled,
      sampleMomentsBudgetCertificate]
  · norm_num [MomentsBudgetCertificate.budgetControlled,
      sampleMomentsBudgetCertificate]

example :
    sampleMomentsBudgetCertificate.certificateBudgetWindow ≤
      sampleMomentsBudgetCertificate.size := by
  apply moments_budgetCertificate_le_size
  constructor
  · norm_num [MomentsBudgetCertificate.controlled,
      sampleMomentsBudgetCertificate]
  · norm_num [MomentsBudgetCertificate.budgetControlled,
      sampleMomentsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MomentsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMomentsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMomentsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.Moments
