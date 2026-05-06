import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Edgeworth schemas.

The finite record tracks expansion order, cumulant budget, and
uniform-error slack.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformEdgeworthSchemas

structure UniformEdgeworthData where
  expansionOrder : ℕ
  cumulantBudget : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def expansionOrderPositive (d : UniformEdgeworthData) : Prop :=
  0 < d.expansionOrder

def cumulantsControlled (d : UniformEdgeworthData) : Prop :=
  d.cumulantBudget ≤ d.expansionOrder + d.errorSlack

def uniformEdgeworthReady (d : UniformEdgeworthData) : Prop :=
  expansionOrderPositive d ∧ cumulantsControlled d

def uniformEdgeworthBudget (d : UniformEdgeworthData) : ℕ :=
  d.expansionOrder + d.cumulantBudget + d.errorSlack

theorem uniformEdgeworthReady.order {d : UniformEdgeworthData}
    (h : uniformEdgeworthReady d) :
    expansionOrderPositive d ∧ cumulantsControlled d ∧
      d.cumulantBudget ≤ uniformEdgeworthBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformEdgeworthBudget
  omega

theorem cumulantBudget_le_edgeworthBudget (d : UniformEdgeworthData) :
    d.cumulantBudget ≤ uniformEdgeworthBudget d := by
  unfold uniformEdgeworthBudget
  omega

def sampleUniformEdgeworthData : UniformEdgeworthData :=
  { expansionOrder := 4, cumulantBudget := 6, errorSlack := 3 }

example : uniformEdgeworthReady sampleUniformEdgeworthData := by
  norm_num [uniformEdgeworthReady, expansionOrderPositive]
  norm_num [cumulantsControlled, sampleUniformEdgeworthData]

example : uniformEdgeworthBudget sampleUniformEdgeworthData = 13 := by
  native_decide

/-- Finite executable readiness audit for uniform Edgeworth data. -/
def uniformEdgeworthDataListReady
    (data : List UniformEdgeworthData) : Bool :=
  data.all fun d =>
    0 < d.expansionOrder && d.cumulantBudget ≤ d.expansionOrder + d.errorSlack

theorem uniformEdgeworthDataList_readyWindow :
    uniformEdgeworthDataListReady
      [{ expansionOrder := 3, cumulantBudget := 4, errorSlack := 1 },
       { expansionOrder := 5, cumulantBudget := 7, errorSlack := 3 }] = true := by
  unfold uniformEdgeworthDataListReady
  native_decide

/-- A certificate window for uniform Edgeworth schemas. -/
structure UniformEdgeworthCertificateWindow where
  expansionWindow : ℕ
  cumulantWindow : ℕ
  errorSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Cumulants are controlled by the expansion window and slack. -/
def uniformEdgeworthCertificateControlled
    (w : UniformEdgeworthCertificateWindow) : Prop :=
  w.cumulantWindow ≤ w.expansionWindow + w.errorSlack + w.slack

/-- Readiness for a uniform Edgeworth certificate. -/
def uniformEdgeworthCertificateReady
    (w : UniformEdgeworthCertificateWindow) : Prop :=
  0 < w.expansionWindow ∧
    uniformEdgeworthCertificateControlled w ∧
      w.certificateBudget ≤ w.expansionWindow + w.cumulantWindow + w.slack

/-- Total size of a uniform Edgeworth certificate. -/
def uniformEdgeworthCertificate
    (w : UniformEdgeworthCertificateWindow) : ℕ :=
  w.expansionWindow + w.cumulantWindow + w.errorSlack +
    w.certificateBudget + w.slack

theorem uniformEdgeworthCertificate_budget_le_certificate
    (w : UniformEdgeworthCertificateWindow)
    (h : uniformEdgeworthCertificateReady w) :
    w.certificateBudget ≤ uniformEdgeworthCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformEdgeworthCertificate
  omega

def sampleUniformEdgeworthCertificateWindow :
    UniformEdgeworthCertificateWindow where
  expansionWindow := 5
  cumulantWindow := 6
  errorSlack := 2
  certificateBudget := 10
  slack := 1

example :
    uniformEdgeworthCertificateReady sampleUniformEdgeworthCertificateWindow := by
  norm_num [uniformEdgeworthCertificateReady,
    uniformEdgeworthCertificateControlled,
    sampleUniformEdgeworthCertificateWindow]

example :
    sampleUniformEdgeworthCertificateWindow.certificateBudget ≤
      uniformEdgeworthCertificate sampleUniformEdgeworthCertificateWindow := by
  apply uniformEdgeworthCertificate_budget_le_certificate
  norm_num [uniformEdgeworthCertificateReady,
    uniformEdgeworthCertificateControlled,
    sampleUniformEdgeworthCertificateWindow]

structure UniformEdgeworthRefinementCertificate where
  expansionWindow : ℕ
  cumulantWindow : ℕ
  errorSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformEdgeworthRefinementCertificate.cumulantControlled
    (c : UniformEdgeworthRefinementCertificate) : Prop :=
  c.cumulantWindow ≤ c.expansionWindow + c.errorSlackWindow + c.slack

def UniformEdgeworthRefinementCertificate.certificateBudgetControlled
    (c : UniformEdgeworthRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.expansionWindow + c.cumulantWindow + c.errorSlackWindow + c.slack

def uniformEdgeworthRefinementReady
    (c : UniformEdgeworthRefinementCertificate) : Prop :=
  0 < c.expansionWindow ∧ c.cumulantControlled ∧ c.certificateBudgetControlled

def UniformEdgeworthRefinementCertificate.size
    (c : UniformEdgeworthRefinementCertificate) : ℕ :=
  c.expansionWindow + c.cumulantWindow + c.errorSlackWindow + c.slack

theorem uniformEdgeworth_certificateBudgetWindow_le_size
    {c : UniformEdgeworthRefinementCertificate}
    (h : uniformEdgeworthRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformEdgeworthRefinementCertificate :
    UniformEdgeworthRefinementCertificate :=
  { expansionWindow := 5, cumulantWindow := 6, errorSlackWindow := 2,
    certificateBudgetWindow := 14, slack := 1 }

example : uniformEdgeworthRefinementReady
    sampleUniformEdgeworthRefinementCertificate := by
  norm_num [uniformEdgeworthRefinementReady,
    UniformEdgeworthRefinementCertificate.cumulantControlled,
    UniformEdgeworthRefinementCertificate.certificateBudgetControlled,
    sampleUniformEdgeworthRefinementCertificate]

example :
    sampleUniformEdgeworthRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformEdgeworthRefinementCertificate.size := by
  norm_num [UniformEdgeworthRefinementCertificate.size,
    sampleUniformEdgeworthRefinementCertificate]

structure UniformEdgeworthBudgetCertificate where
  expansionWindow : ℕ
  cumulantWindow : ℕ
  errorSlackWindow : ℕ
  edgeworthBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformEdgeworthBudgetCertificate.controlled
    (c : UniformEdgeworthBudgetCertificate) : Prop :=
  0 < c.expansionWindow ∧
    c.cumulantWindow ≤ c.expansionWindow + c.errorSlackWindow + c.slack ∧
      c.edgeworthBudgetWindow ≤
        c.expansionWindow + c.cumulantWindow + c.errorSlackWindow + c.slack

def UniformEdgeworthBudgetCertificate.budgetControlled
    (c : UniformEdgeworthBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.expansionWindow + c.cumulantWindow + c.errorSlackWindow +
      c.edgeworthBudgetWindow + c.slack

def UniformEdgeworthBudgetCertificate.Ready
    (c : UniformEdgeworthBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformEdgeworthBudgetCertificate.size
    (c : UniformEdgeworthBudgetCertificate) : ℕ :=
  c.expansionWindow + c.cumulantWindow + c.errorSlackWindow +
    c.edgeworthBudgetWindow + c.slack

theorem uniformEdgeworth_budgetCertificate_le_size
    (c : UniformEdgeworthBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformEdgeworthBudgetCertificate :
    UniformEdgeworthBudgetCertificate :=
  { expansionWindow := 5
    cumulantWindow := 6
    errorSlackWindow := 2
    edgeworthBudgetWindow := 14
    certificateBudgetWindow := 28
    slack := 1 }

example : sampleUniformEdgeworthBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformEdgeworthBudgetCertificate.controlled,
      sampleUniformEdgeworthBudgetCertificate]
  · norm_num [UniformEdgeworthBudgetCertificate.budgetControlled,
      sampleUniformEdgeworthBudgetCertificate]

example :
    sampleUniformEdgeworthBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformEdgeworthBudgetCertificate.size := by
  apply uniformEdgeworth_budgetCertificate_le_size
  constructor
  · norm_num [UniformEdgeworthBudgetCertificate.controlled,
      sampleUniformEdgeworthBudgetCertificate]
  · norm_num [UniformEdgeworthBudgetCertificate.budgetControlled,
      sampleUniformEdgeworthBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformEdgeworthBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformEdgeworthBudgetCertificate.controlled,
      sampleUniformEdgeworthBudgetCertificate]
  · norm_num [UniformEdgeworthBudgetCertificate.budgetControlled,
      sampleUniformEdgeworthBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformEdgeworthBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformEdgeworthBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformEdgeworthBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformEdgeworthBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformEdgeworthBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformEdgeworthSchemas
