import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform exponential integral schemas.

This module records finite bookkeeping for exponential integral windows.
-/

namespace AnalyticCombinatorics.PartB.Ch8.UniformExponentialIntegralSchemas

structure ExponentialIntegralData where
  integralScale : ℕ
  tailWindow : ℕ
  exponentialSlack : ℕ
deriving DecidableEq, Repr

def hasIntegralScale (d : ExponentialIntegralData) : Prop :=
  0 < d.integralScale

def tailWindowControlled (d : ExponentialIntegralData) : Prop :=
  d.tailWindow ≤ d.integralScale + d.exponentialSlack

def exponentialIntegralReady (d : ExponentialIntegralData) : Prop :=
  hasIntegralScale d ∧ tailWindowControlled d

def exponentialIntegralBudget (d : ExponentialIntegralData) : ℕ :=
  d.integralScale + d.tailWindow + d.exponentialSlack

theorem exponentialIntegralReady.hasIntegralScale
    {d : ExponentialIntegralData}
    (h : exponentialIntegralReady d) :
    hasIntegralScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem tailWindow_le_budget (d : ExponentialIntegralData) :
    d.tailWindow ≤ exponentialIntegralBudget d := by
  unfold exponentialIntegralBudget
  omega

def sampleExponentialIntegralData : ExponentialIntegralData :=
  { integralScale := 6, tailWindow := 8, exponentialSlack := 3 }

example : exponentialIntegralReady sampleExponentialIntegralData := by
  norm_num [exponentialIntegralReady, hasIntegralScale]
  norm_num [tailWindowControlled, sampleExponentialIntegralData]

example : exponentialIntegralBudget sampleExponentialIntegralData = 17 := by
  native_decide

/-- Finite executable readiness audit for exponential integral windows. -/
def exponentialIntegralListReady
    (windows : List ExponentialIntegralData) : Bool :=
  windows.all fun d =>
    0 < d.integralScale && d.tailWindow ≤ d.integralScale + d.exponentialSlack

theorem exponentialIntegralList_readyWindow :
    exponentialIntegralListReady
      [{ integralScale := 4, tailWindow := 5, exponentialSlack := 1 },
       { integralScale := 6, tailWindow := 8, exponentialSlack := 3 }] = true := by
  unfold exponentialIntegralListReady
  native_decide

structure ExponentialIntegralBudgetCertificate where
  integralScaleWindow : ℕ
  tailWindow : ℕ
  exponentialSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExponentialIntegralBudgetCertificate.controlled
    (c : ExponentialIntegralBudgetCertificate) : Prop :=
  0 < c.integralScaleWindow ∧
    c.tailWindow ≤ c.integralScaleWindow + c.exponentialSlackWindow + c.slack

def ExponentialIntegralBudgetCertificate.budgetControlled
    (c : ExponentialIntegralBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.integralScaleWindow + c.tailWindow + c.exponentialSlackWindow + c.slack

def ExponentialIntegralBudgetCertificate.Ready
    (c : ExponentialIntegralBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ExponentialIntegralBudgetCertificate.size
    (c : ExponentialIntegralBudgetCertificate) : ℕ :=
  c.integralScaleWindow + c.tailWindow + c.exponentialSlackWindow + c.slack

theorem exponentialIntegral_budgetCertificate_le_size
    (c : ExponentialIntegralBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleExponentialIntegralBudgetCertificate :
    ExponentialIntegralBudgetCertificate :=
  { integralScaleWindow := 6
    tailWindow := 8
    exponentialSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleExponentialIntegralBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialIntegralBudgetCertificate.controlled,
      sampleExponentialIntegralBudgetCertificate]
  · norm_num [ExponentialIntegralBudgetCertificate.budgetControlled,
      sampleExponentialIntegralBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleExponentialIntegralBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialIntegralBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleExponentialIntegralBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialIntegralBudgetCertificate.controlled,
      sampleExponentialIntegralBudgetCertificate]
  · norm_num [ExponentialIntegralBudgetCertificate.budgetControlled,
      sampleExponentialIntegralBudgetCertificate]

example :
    sampleExponentialIntegralBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialIntegralBudgetCertificate.size := by
  apply exponentialIntegral_budgetCertificate_le_size
  constructor
  · norm_num [ExponentialIntegralBudgetCertificate.controlled,
      sampleExponentialIntegralBudgetCertificate]
  · norm_num [ExponentialIntegralBudgetCertificate.budgetControlled,
      sampleExponentialIntegralBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List ExponentialIntegralBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleExponentialIntegralBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleExponentialIntegralBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch8.UniformExponentialIntegralSchemas
