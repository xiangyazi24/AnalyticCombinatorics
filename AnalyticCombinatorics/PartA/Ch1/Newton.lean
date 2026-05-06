import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Newton polygon bookkeeping.
-/

namespace AnalyticCombinatorics.PartA.Ch1.Newton

structure NewtonSlopeData where
  lowerOrder : ℕ
  upperOrder : ℕ
  slopeSlack : ℕ
deriving DecidableEq, Repr

def newtonReady (d : NewtonSlopeData) : Prop :=
  d.lowerOrder ≤ d.upperOrder + d.slopeSlack

def newtonBudget (d : NewtonSlopeData) : ℕ :=
  d.lowerOrder + d.upperOrder + d.slopeSlack

theorem lowerOrder_le_budget (d : NewtonSlopeData) :
    d.lowerOrder ≤ newtonBudget d := by
  unfold newtonBudget
  omega

def sampleNewtonSlopeData : NewtonSlopeData :=
  { lowerOrder := 5, upperOrder := 4, slopeSlack := 2 }

example : newtonReady sampleNewtonSlopeData := by
  norm_num [newtonReady, sampleNewtonSlopeData]

structure NewtonPoint where
  exponent : ℕ
  valuation : ℕ
deriving DecidableEq, Repr

structure NewtonWindow where
  left : NewtonPoint
  right : NewtonPoint
  horizontalSlack : ℕ
  verticalSlack : ℕ
deriving DecidableEq, Repr

def NewtonWindow.horizontalSpan (w : NewtonWindow) : ℕ :=
  w.right.exponent - w.left.exponent

def NewtonWindow.verticalDrop (w : NewtonWindow) : ℕ :=
  w.left.valuation - w.right.valuation

def NewtonWindow.ordered (w : NewtonWindow) : Prop :=
  w.left.exponent ≤ w.right.exponent + w.horizontalSlack ∧
    w.right.valuation ≤ w.left.valuation + w.verticalSlack

def NewtonWindow.slopeNumerator (w : NewtonWindow) : ℕ :=
  w.verticalDrop + w.verticalSlack

def NewtonWindow.slopeDenominator (w : NewtonWindow) : ℕ :=
  w.horizontalSpan + 1

def NewtonWindow.certificate (w : NewtonWindow) : ℕ :=
  w.left.exponent + w.left.valuation + w.right.exponent + w.right.valuation +
    w.horizontalSlack + w.verticalSlack

theorem horizontalSlack_le_certificate (w : NewtonWindow) :
    w.horizontalSlack ≤ w.certificate := by
  unfold NewtonWindow.certificate
  omega

theorem verticalSlack_le_certificate (w : NewtonWindow) :
    w.verticalSlack ≤ w.certificate := by
  unfold NewtonWindow.certificate
  omega

def sampleNewtonWindow : NewtonWindow :=
  { left := { exponent := 2, valuation := 7 },
    right := { exponent := 6, valuation := 3 },
    horizontalSlack := 0,
    verticalSlack := 1 }

example : sampleNewtonWindow.ordered := by
  norm_num [sampleNewtonWindow, NewtonWindow.ordered]

example : sampleNewtonWindow.slopeNumerator = 5 := by
  norm_num [sampleNewtonWindow, NewtonWindow.slopeNumerator, NewtonWindow.verticalDrop]

example : sampleNewtonWindow.slopeDenominator = 5 := by
  norm_num [sampleNewtonWindow, NewtonWindow.slopeDenominator, NewtonWindow.horizontalSpan]


structure NewtonBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def NewtonBudgetCertificate.controlled
    (c : NewtonBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def NewtonBudgetCertificate.budgetControlled
    (c : NewtonBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def NewtonBudgetCertificate.Ready
    (c : NewtonBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def NewtonBudgetCertificate.size
    (c : NewtonBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem newton_budgetCertificate_le_size
    (c : NewtonBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleNewtonBudgetCertificate :
    NewtonBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleNewtonBudgetCertificate.Ready := by
  constructor
  · norm_num [NewtonBudgetCertificate.controlled,
      sampleNewtonBudgetCertificate]
  · norm_num [NewtonBudgetCertificate.budgetControlled,
      sampleNewtonBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleNewtonBudgetCertificate.certificateBudgetWindow ≤
      sampleNewtonBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleNewtonBudgetCertificate.Ready := by
  constructor
  · norm_num [NewtonBudgetCertificate.controlled,
      sampleNewtonBudgetCertificate]
  · norm_num [NewtonBudgetCertificate.budgetControlled,
      sampleNewtonBudgetCertificate]

example :
    sampleNewtonBudgetCertificate.certificateBudgetWindow ≤
      sampleNewtonBudgetCertificate.size := by
  apply newton_budgetCertificate_le_size
  constructor
  · norm_num [NewtonBudgetCertificate.controlled,
      sampleNewtonBudgetCertificate]
  · norm_num [NewtonBudgetCertificate.budgetControlled,
      sampleNewtonBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List NewtonBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleNewtonBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleNewtonBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.Newton
