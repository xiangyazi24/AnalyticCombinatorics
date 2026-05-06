import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Asymptotic scale hierarchy bookkeeping.

The module records finite dominance chains between three scale levels.
-/

namespace AnalyticCombinatorics.Asymptotics.AsymptoticScaleHierarchy

structure ScaleHierarchy where
  smallScale : ℕ
  middleScale : ℕ
  largeScale : ℕ
deriving DecidableEq, Repr

def hierarchySeparated (s : ScaleHierarchy) : Prop :=
  s.smallScale ≤ s.middleScale ∧ s.middleScale ≤ s.largeScale

def strictHierarchy (s : ScaleHierarchy) : Prop :=
  s.smallScale < s.middleScale ∧ s.middleScale < s.largeScale

def hierarchyWidth (s : ScaleHierarchy) : ℕ :=
  s.largeScale - s.smallScale

theorem strictHierarchy.separated {s : ScaleHierarchy}
    (h : strictHierarchy s) :
    hierarchySeparated s := by
  unfold strictHierarchy hierarchySeparated at *
  exact ⟨le_of_lt h.1, le_of_lt h.2⟩

theorem hierarchyWidth_add {s : ScaleHierarchy}
    (h : hierarchySeparated s) :
    hierarchyWidth s + s.smallScale = s.largeScale := by
  unfold hierarchySeparated hierarchyWidth at *
  omega

def sampleHierarchy : ScaleHierarchy :=
  { smallScale := 2, middleScale := 5, largeScale := 11 }

example : strictHierarchy sampleHierarchy := by
  norm_num [strictHierarchy, sampleHierarchy]

example : hierarchyWidth sampleHierarchy = 9 := by
  native_decide

/-- Finite executable readiness audit for asymptotic scale hierarchies. -/
def scaleHierarchyListReady (windows : List ScaleHierarchy) : Bool :=
  windows.all fun s =>
    s.smallScale < s.middleScale && s.middleScale < s.largeScale

theorem scaleHierarchyList_readyWindow :
    scaleHierarchyListReady
      [{ smallScale := 1, middleScale := 3, largeScale := 7 },
       { smallScale := 2, middleScale := 5, largeScale := 11 }] = true := by
  unfold scaleHierarchyListReady
  native_decide

structure ScaleHierarchyWindow where
  smallScale : ℕ
  middleScale : ℕ
  largeScale : ℕ
  separationSlack : ℕ
deriving DecidableEq, Repr

def ScaleHierarchyWindow.ordered (w : ScaleHierarchyWindow) : Prop :=
  w.smallScale ≤ w.middleScale ∧ w.middleScale ≤ w.largeScale

def ScaleHierarchyWindow.separated (w : ScaleHierarchyWindow) : Prop :=
  w.smallScale + w.separationSlack < w.largeScale

def ScaleHierarchyWindow.ready (w : ScaleHierarchyWindow) : Prop :=
  w.ordered ∧ w.separated

def ScaleHierarchyWindow.certificate (w : ScaleHierarchyWindow) : ℕ :=
  w.smallScale + w.middleScale + w.largeScale + w.separationSlack

theorem largeScale_le_certificate (w : ScaleHierarchyWindow) :
    w.largeScale ≤ w.certificate := by
  unfold ScaleHierarchyWindow.certificate
  omega

def sampleScaleHierarchyWindow : ScaleHierarchyWindow :=
  { smallScale := 2, middleScale := 5, largeScale := 11, separationSlack := 1 }

example : sampleScaleHierarchyWindow.ready := by
  norm_num [sampleScaleHierarchyWindow, ScaleHierarchyWindow.ready,
    ScaleHierarchyWindow.ordered, ScaleHierarchyWindow.separated]

/-- A refinement certificate for finite scale hierarchies. -/
structure ScaleHierarchyCertificate where
  smallWindow : ℕ
  middleWindow : ℕ
  largeWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The three scale windows are ordered and separated by slack. -/
def scaleHierarchyCertificateControlled
    (w : ScaleHierarchyCertificate) : Prop :=
  w.smallWindow ≤ w.middleWindow ∧
    w.middleWindow ≤ w.largeWindow ∧
      w.smallWindow + w.slack < w.largeWindow

/-- Readiness for a scale hierarchy certificate. -/
def scaleHierarchyCertificateReady
    (w : ScaleHierarchyCertificate) : Prop :=
  scaleHierarchyCertificateControlled w ∧
    w.certificateBudget ≤ w.smallWindow + w.middleWindow + w.largeWindow + w.slack

/-- Total size of a scale hierarchy certificate. -/
def scaleHierarchyCertificateSize
    (w : ScaleHierarchyCertificate) : ℕ :=
  w.smallWindow + w.middleWindow + w.largeWindow + w.certificateBudget + w.slack

theorem scaleHierarchyCertificate_budget_le_size
    (w : ScaleHierarchyCertificate)
    (h : scaleHierarchyCertificateReady w) :
    w.certificateBudget ≤ scaleHierarchyCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold scaleHierarchyCertificateSize
  omega

def sampleScaleHierarchyCertificate : ScaleHierarchyCertificate where
  smallWindow := 2
  middleWindow := 5
  largeWindow := 11
  certificateBudget := 18
  slack := 1

example :
    scaleHierarchyCertificateReady sampleScaleHierarchyCertificate := by
  norm_num [scaleHierarchyCertificateReady,
    scaleHierarchyCertificateControlled, sampleScaleHierarchyCertificate]

example :
    sampleScaleHierarchyCertificate.certificateBudget ≤
      scaleHierarchyCertificateSize sampleScaleHierarchyCertificate := by
  apply scaleHierarchyCertificate_budget_le_size
  norm_num [scaleHierarchyCertificateReady,
    scaleHierarchyCertificateControlled, sampleScaleHierarchyCertificate]

/-- A refinement certificate with the scale-chain budget separated from size. -/
structure ScaleHierarchyRefinementCertificate where
  smallWindow : ℕ
  middleWindow : ℕ
  largeWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def ScaleHierarchyRefinementCertificate.chainControlled
    (cert : ScaleHierarchyRefinementCertificate) : Prop :=
  cert.smallWindow ≤ cert.middleWindow ∧
    cert.middleWindow ≤ cert.largeWindow ∧
      cert.smallWindow + cert.slack < cert.largeWindow

def ScaleHierarchyRefinementCertificate.budgetControlled
    (cert : ScaleHierarchyRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.smallWindow + cert.middleWindow + cert.largeWindow + cert.slack

def scaleHierarchyRefinementReady
    (cert : ScaleHierarchyRefinementCertificate) : Prop :=
  cert.chainControlled ∧ cert.budgetControlled

def ScaleHierarchyRefinementCertificate.size
    (cert : ScaleHierarchyRefinementCertificate) : ℕ :=
  cert.smallWindow + cert.middleWindow + cert.largeWindow + cert.slack

theorem scaleHierarchy_certificateBudgetWindow_le_size
    (cert : ScaleHierarchyRefinementCertificate)
    (h : scaleHierarchyRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleScaleHierarchyRefinementCertificate :
    ScaleHierarchyRefinementCertificate where
  smallWindow := 2
  middleWindow := 5
  largeWindow := 11
  certificateBudgetWindow := 19
  slack := 1

example :
    scaleHierarchyRefinementReady sampleScaleHierarchyRefinementCertificate := by
  norm_num [scaleHierarchyRefinementReady,
    ScaleHierarchyRefinementCertificate.chainControlled,
    ScaleHierarchyRefinementCertificate.budgetControlled,
    sampleScaleHierarchyRefinementCertificate]

example :
    sampleScaleHierarchyRefinementCertificate.certificateBudgetWindow ≤
      sampleScaleHierarchyRefinementCertificate.size := by
  apply scaleHierarchy_certificateBudgetWindow_le_size
  norm_num [scaleHierarchyRefinementReady,
    ScaleHierarchyRefinementCertificate.chainControlled,
    ScaleHierarchyRefinementCertificate.budgetControlled,
    sampleScaleHierarchyRefinementCertificate]


structure AsymptoticScaleHierarchyBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AsymptoticScaleHierarchyBudgetCertificate.controlled
    (c : AsymptoticScaleHierarchyBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def AsymptoticScaleHierarchyBudgetCertificate.budgetControlled
    (c : AsymptoticScaleHierarchyBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AsymptoticScaleHierarchyBudgetCertificate.Ready
    (c : AsymptoticScaleHierarchyBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AsymptoticScaleHierarchyBudgetCertificate.size
    (c : AsymptoticScaleHierarchyBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem asymptoticScaleHierarchy_budgetCertificate_le_size
    (c : AsymptoticScaleHierarchyBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAsymptoticScaleHierarchyBudgetCertificate :
    AsymptoticScaleHierarchyBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleAsymptoticScaleHierarchyBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticScaleHierarchyBudgetCertificate.controlled,
      sampleAsymptoticScaleHierarchyBudgetCertificate]
  · norm_num [AsymptoticScaleHierarchyBudgetCertificate.budgetControlled,
      sampleAsymptoticScaleHierarchyBudgetCertificate]

example :
    sampleAsymptoticScaleHierarchyBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticScaleHierarchyBudgetCertificate.size := by
  apply asymptoticScaleHierarchy_budgetCertificate_le_size
  constructor
  · norm_num [AsymptoticScaleHierarchyBudgetCertificate.controlled,
      sampleAsymptoticScaleHierarchyBudgetCertificate]
  · norm_num [AsymptoticScaleHierarchyBudgetCertificate.budgetControlled,
      sampleAsymptoticScaleHierarchyBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAsymptoticScaleHierarchyBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticScaleHierarchyBudgetCertificate.controlled,
      sampleAsymptoticScaleHierarchyBudgetCertificate]
  · norm_num [AsymptoticScaleHierarchyBudgetCertificate.budgetControlled,
      sampleAsymptoticScaleHierarchyBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAsymptoticScaleHierarchyBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticScaleHierarchyBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AsymptoticScaleHierarchyBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAsymptoticScaleHierarchyBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAsymptoticScaleHierarchyBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.AsymptoticScaleHierarchy
