import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite orbit counting models.

The finite record stores group actions, orbit count, and stabilizer
slack.
-/

namespace AnalyticCombinatorics.AppA.FiniteOrbitCountingModels

structure OrbitCountingData where
  actionCount : ℕ
  orbitCount : ℕ
  stabilizerSlack : ℕ
deriving DecidableEq, Repr

def actionCountPositive (d : OrbitCountingData) : Prop :=
  0 < d.actionCount

def orbitCountControlled (d : OrbitCountingData) : Prop :=
  d.orbitCount ≤ d.actionCount + d.stabilizerSlack

def orbitCountingReady (d : OrbitCountingData) : Prop :=
  actionCountPositive d ∧ orbitCountControlled d

def orbitCountingBudget (d : OrbitCountingData) : ℕ :=
  d.actionCount + d.orbitCount + d.stabilizerSlack

theorem orbitCountingReady.actions {d : OrbitCountingData}
    (h : orbitCountingReady d) :
    actionCountPositive d ∧ orbitCountControlled d ∧ d.orbitCount ≤ orbitCountingBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold orbitCountingBudget
  omega

theorem orbitCount_le_orbitCountingBudget (d : OrbitCountingData) :
    d.orbitCount ≤ orbitCountingBudget d := by
  unfold orbitCountingBudget
  omega

def sampleOrbitCountingData : OrbitCountingData :=
  { actionCount := 7, orbitCount := 9, stabilizerSlack := 3 }

example : orbitCountingReady sampleOrbitCountingData := by
  norm_num [orbitCountingReady, actionCountPositive]
  norm_num [orbitCountControlled, sampleOrbitCountingData]

example : orbitCountingBudget sampleOrbitCountingData = 19 := by
  native_decide

structure OrbitCountingWindow where
  actionCount : ℕ
  orbitCount : ℕ
  stabilizerSlack : ℕ
  quotientBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def OrbitCountingWindow.orbitControlled (w : OrbitCountingWindow) : Prop :=
  w.orbitCount ≤ w.actionCount + w.stabilizerSlack + w.slack

def OrbitCountingWindow.quotientControlled (w : OrbitCountingWindow) : Prop :=
  w.quotientBudget ≤ w.actionCount + w.orbitCount + w.stabilizerSlack + w.slack

def orbitCountingWindowReady (w : OrbitCountingWindow) : Prop :=
  0 < w.actionCount ∧
    w.orbitControlled ∧
    w.quotientControlled

def OrbitCountingWindow.certificate (w : OrbitCountingWindow) : ℕ :=
  w.actionCount + w.orbitCount + w.stabilizerSlack + w.slack

theorem orbitCounting_quotientBudget_le_certificate {w : OrbitCountingWindow}
    (h : orbitCountingWindowReady w) :
    w.quotientBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hquotient⟩
  exact hquotient

def sampleOrbitCountingWindow : OrbitCountingWindow :=
  { actionCount := 7, orbitCount := 9, stabilizerSlack := 3, quotientBudget := 18, slack := 0 }

example : orbitCountingWindowReady sampleOrbitCountingWindow := by
  norm_num [orbitCountingWindowReady, OrbitCountingWindow.orbitControlled,
    OrbitCountingWindow.quotientControlled, sampleOrbitCountingWindow]

example : sampleOrbitCountingWindow.certificate = 19 := by
  native_decide


structure FiniteOrbitCountingModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteOrbitCountingModelsBudgetCertificate.controlled
    (c : FiniteOrbitCountingModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteOrbitCountingModelsBudgetCertificate.budgetControlled
    (c : FiniteOrbitCountingModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteOrbitCountingModelsBudgetCertificate.Ready
    (c : FiniteOrbitCountingModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteOrbitCountingModelsBudgetCertificate.size
    (c : FiniteOrbitCountingModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteOrbitCountingModels_budgetCertificate_le_size
    (c : FiniteOrbitCountingModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteOrbitCountingModelsBudgetCertificate :
    FiniteOrbitCountingModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteOrbitCountingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteOrbitCountingModelsBudgetCertificate.controlled,
      sampleFiniteOrbitCountingModelsBudgetCertificate]
  · norm_num [FiniteOrbitCountingModelsBudgetCertificate.budgetControlled,
      sampleFiniteOrbitCountingModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteOrbitCountingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteOrbitCountingModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteOrbitCountingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteOrbitCountingModelsBudgetCertificate.controlled,
      sampleFiniteOrbitCountingModelsBudgetCertificate]
  · norm_num [FiniteOrbitCountingModelsBudgetCertificate.budgetControlled,
      sampleFiniteOrbitCountingModelsBudgetCertificate]

example :
    sampleFiniteOrbitCountingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteOrbitCountingModelsBudgetCertificate.size := by
  apply finiteOrbitCountingModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteOrbitCountingModelsBudgetCertificate.controlled,
      sampleFiniteOrbitCountingModelsBudgetCertificate]
  · norm_num [FiniteOrbitCountingModelsBudgetCertificate.budgetControlled,
      sampleFiniteOrbitCountingModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteOrbitCountingModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteOrbitCountingModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteOrbitCountingModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteOrbitCountingModels
