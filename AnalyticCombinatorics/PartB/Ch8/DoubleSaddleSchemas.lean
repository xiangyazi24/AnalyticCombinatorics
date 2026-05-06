import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Double saddle schemas.

The finite schema tracks two saddle neighborhoods and a shared error
budget.
-/

namespace AnalyticCombinatorics.PartB.Ch8.DoubleSaddleSchemas

structure DoubleSaddleData where
  firstWindow : ℕ
  secondWindow : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def firstWindowNonempty (d : DoubleSaddleData) : Prop :=
  0 < d.firstWindow

def secondWindowControlled (d : DoubleSaddleData) : Prop :=
  d.secondWindow ≤ d.firstWindow + d.errorBudget

def doubleSaddleReady (d : DoubleSaddleData) : Prop :=
  firstWindowNonempty d ∧ secondWindowControlled d

def doubleSaddleBudget (d : DoubleSaddleData) : ℕ :=
  d.firstWindow + d.secondWindow + d.errorBudget

theorem doubleSaddleReady.first {d : DoubleSaddleData}
    (h : doubleSaddleReady d) :
    firstWindowNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem secondWindow_le_doubleSaddleBudget (d : DoubleSaddleData) :
    d.secondWindow ≤ doubleSaddleBudget d := by
  unfold doubleSaddleBudget
  omega

def sampleDoubleSaddleData : DoubleSaddleData :=
  { firstWindow := 5, secondWindow := 8, errorBudget := 4 }

example : doubleSaddleReady sampleDoubleSaddleData := by
  norm_num [doubleSaddleReady, firstWindowNonempty]
  norm_num [secondWindowControlled, sampleDoubleSaddleData]

example : doubleSaddleBudget sampleDoubleSaddleData = 17 := by
  native_decide

structure DoubleSaddleWindow where
  firstWindow : ℕ
  secondWindow : ℕ
  errorBudget : ℕ
  matchingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DoubleSaddleWindow.secondControlled (w : DoubleSaddleWindow) : Prop :=
  w.secondWindow ≤ w.firstWindow + w.errorBudget + w.slack

def DoubleSaddleWindow.matchingControlled (w : DoubleSaddleWindow) : Prop :=
  w.matchingBudget ≤ w.firstWindow + w.secondWindow + w.errorBudget + w.slack

def doubleSaddleWindowReady (w : DoubleSaddleWindow) : Prop :=
  0 < w.firstWindow ∧
    w.secondControlled ∧
    w.matchingControlled

def DoubleSaddleWindow.certificate (w : DoubleSaddleWindow) : ℕ :=
  w.firstWindow + w.secondWindow + w.errorBudget + w.slack

theorem doubleSaddle_matchingBudget_le_certificate {w : DoubleSaddleWindow}
    (h : doubleSaddleWindowReady w) :
    w.matchingBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hmatching⟩
  exact hmatching

def sampleDoubleSaddleWindow : DoubleSaddleWindow :=
  { firstWindow := 5, secondWindow := 8, errorBudget := 4, matchingBudget := 16, slack := 0 }

example : doubleSaddleWindowReady sampleDoubleSaddleWindow := by
  norm_num [doubleSaddleWindowReady, DoubleSaddleWindow.secondControlled,
    DoubleSaddleWindow.matchingControlled, sampleDoubleSaddleWindow]

example : sampleDoubleSaddleWindow.certificate = 17 := by
  native_decide


structure DoubleSaddleSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DoubleSaddleSchemasBudgetCertificate.controlled
    (c : DoubleSaddleSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DoubleSaddleSchemasBudgetCertificate.budgetControlled
    (c : DoubleSaddleSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DoubleSaddleSchemasBudgetCertificate.Ready
    (c : DoubleSaddleSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DoubleSaddleSchemasBudgetCertificate.size
    (c : DoubleSaddleSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem doubleSaddleSchemas_budgetCertificate_le_size
    (c : DoubleSaddleSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDoubleSaddleSchemasBudgetCertificate :
    DoubleSaddleSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDoubleSaddleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DoubleSaddleSchemasBudgetCertificate.controlled,
      sampleDoubleSaddleSchemasBudgetCertificate]
  · norm_num [DoubleSaddleSchemasBudgetCertificate.budgetControlled,
      sampleDoubleSaddleSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDoubleSaddleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDoubleSaddleSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDoubleSaddleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DoubleSaddleSchemasBudgetCertificate.controlled,
      sampleDoubleSaddleSchemasBudgetCertificate]
  · norm_num [DoubleSaddleSchemasBudgetCertificate.budgetControlled,
      sampleDoubleSaddleSchemasBudgetCertificate]

example :
    sampleDoubleSaddleSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDoubleSaddleSchemasBudgetCertificate.size := by
  apply doubleSaddleSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DoubleSaddleSchemasBudgetCertificate.controlled,
      sampleDoubleSaddleSchemasBudgetCertificate]
  · norm_num [DoubleSaddleSchemasBudgetCertificate.budgetControlled,
      sampleDoubleSaddleSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List DoubleSaddleSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDoubleSaddleSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDoubleSaddleSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.DoubleSaddleSchemas
