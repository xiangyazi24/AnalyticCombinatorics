import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic sheaf bookkeeping models.

The file records finite local section counts, overlap constraints, and
gluing budgets.
-/

namespace AnalyticCombinatorics.AppB.AnalyticSheafModels

structure SheafDatum where
  localSectionCount : ℕ
  overlapCount : ℕ
  gluingBudget : ℕ
deriving DecidableEq, Repr

def nonemptySections (d : SheafDatum) : Prop :=
  0 < d.localSectionCount

def overlapsControlled (d : SheafDatum) : Prop :=
  d.overlapCount ≤ d.localSectionCount + d.gluingBudget

def sheafReady (d : SheafDatum) : Prop :=
  nonemptySections d ∧ overlapsControlled d

def sheafComplexity (d : SheafDatum) : ℕ :=
  d.localSectionCount + d.overlapCount + d.gluingBudget

theorem sheafReady.sections {d : SheafDatum}
    (h : sheafReady d) :
    nonemptySections d ∧ overlapsControlled d ∧
      d.localSectionCount ≤ sheafComplexity d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold sheafComplexity
  omega

theorem localSectionCount_le_complexity (d : SheafDatum) :
    d.localSectionCount ≤ sheafComplexity d := by
  unfold sheafComplexity
  omega

def sampleSheaf : SheafDatum :=
  { localSectionCount := 4, overlapCount := 5, gluingBudget := 2 }

example : sheafReady sampleSheaf := by
  norm_num [sheafReady, nonemptySections, overlapsControlled, sampleSheaf]

example : sheafComplexity sampleSheaf = 11 := by
  native_decide

structure SheafWindow where
  sectionWindow : ℕ
  overlapWindow : ℕ
  gluingWindow : ℕ
  sheafBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SheafWindow.overlapControlled (w : SheafWindow) : Prop :=
  w.overlapWindow ≤ w.sectionWindow + w.gluingWindow + w.slack

def sheafWindowReady (w : SheafWindow) : Prop :=
  0 < w.sectionWindow ∧ w.overlapControlled ∧
    w.sheafBudget ≤ w.sectionWindow + w.overlapWindow + w.gluingWindow + w.slack

def SheafWindow.certificate (w : SheafWindow) : ℕ :=
  w.sectionWindow + w.overlapWindow + w.gluingWindow + w.sheafBudget + w.slack

theorem sheaf_sheafBudget_le_certificate (w : SheafWindow) :
    w.sheafBudget ≤ w.certificate := by
  unfold SheafWindow.certificate
  omega

def sampleSheafWindow : SheafWindow :=
  { sectionWindow := 4, overlapWindow := 5, gluingWindow := 2, sheafBudget := 12, slack := 1 }

example : sheafWindowReady sampleSheafWindow := by
  norm_num [sheafWindowReady, SheafWindow.overlapControlled, sampleSheafWindow]


structure AnalyticSheafModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticSheafModelsBudgetCertificate.controlled
    (c : AnalyticSheafModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticSheafModelsBudgetCertificate.budgetControlled
    (c : AnalyticSheafModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticSheafModelsBudgetCertificate.Ready
    (c : AnalyticSheafModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticSheafModelsBudgetCertificate.size
    (c : AnalyticSheafModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticSheafModels_budgetCertificate_le_size
    (c : AnalyticSheafModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticSheafModelsBudgetCertificate :
    AnalyticSheafModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticSheafModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticSheafModelsBudgetCertificate.controlled,
      sampleAnalyticSheafModelsBudgetCertificate]
  · norm_num [AnalyticSheafModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSheafModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticSheafModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticSheafModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticSheafModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticSheafModelsBudgetCertificate.controlled,
      sampleAnalyticSheafModelsBudgetCertificate]
  · norm_num [AnalyticSheafModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSheafModelsBudgetCertificate]

example :
    sampleAnalyticSheafModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticSheafModelsBudgetCertificate.size := by
  apply analyticSheafModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticSheafModelsBudgetCertificate.controlled,
      sampleAnalyticSheafModelsBudgetCertificate]
  · norm_num [AnalyticSheafModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSheafModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticSheafModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticSheafModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticSheafModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticSheafModels
