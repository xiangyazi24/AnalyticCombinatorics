import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Scale separation algebra.

The finite data records lower, middle, and upper scales together with
separation gaps.
-/

namespace AnalyticCombinatorics.Asymptotics.ScaleSeparationAlgebra

structure SeparatedScales where
  lowerScale : ℕ
  middleScale : ℕ
  upperScale : ℕ
deriving DecidableEq, Repr

def weaklySeparated (s : SeparatedScales) : Prop :=
  s.lowerScale ≤ s.middleScale ∧ s.middleScale ≤ s.upperScale

def lowerGap (s : SeparatedScales) : ℕ :=
  s.middleScale - s.lowerScale

def upperGap (s : SeparatedScales) : ℕ :=
  s.upperScale - s.middleScale

theorem weaklySeparated.lower_gap_add {s : SeparatedScales}
    (h : weaklySeparated s) :
    lowerGap s + s.lowerScale = s.middleScale := by
  unfold weaklySeparated lowerGap at *
  omega

theorem weaklySeparated.upper_gap_add {s : SeparatedScales}
    (h : weaklySeparated s) :
    upperGap s + s.middleScale = s.upperScale := by
  unfold weaklySeparated upperGap at *
  omega

def sampleSeparatedScales : SeparatedScales :=
  { lowerScale := 2, middleScale := 5, upperScale := 11 }

example : weaklySeparated sampleSeparatedScales := by
  norm_num [weaklySeparated, sampleSeparatedScales]

example : lowerGap sampleSeparatedScales = 3 := by
  native_decide

example : upperGap sampleSeparatedScales = 6 := by
  native_decide

/-- Finite executable readiness audit for separated scale triples. -/
def separatedScalesListReady (scales : List SeparatedScales) : Bool :=
  scales.all fun s => s.lowerScale ≤ s.middleScale && s.middleScale ≤ s.upperScale

theorem separatedScalesList_readyWindow :
    separatedScalesListReady
      [{ lowerScale := 1, middleScale := 3, upperScale := 5 },
       { lowerScale := 2, middleScale := 5, upperScale := 11 }] = true := by
  unfold separatedScalesListReady
  native_decide

structure ScaleSeparationWindow where
  lowerScale : ℕ
  middleScale : ℕ
  upperScale : ℕ
  separationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ScaleSeparationWindow.ordered (w : ScaleSeparationWindow) : Prop :=
  w.lowerScale ≤ w.middleScale ∧ w.middleScale ≤ w.upperScale + w.slack

def ScaleSeparationWindow.separationControlled (w : ScaleSeparationWindow) : Prop :=
  w.separationBudget ≤ w.lowerScale + w.middleScale + w.upperScale + w.slack

def scaleSeparationWindowReady (w : ScaleSeparationWindow) : Prop :=
  w.ordered ∧ w.separationControlled

def ScaleSeparationWindow.certificate (w : ScaleSeparationWindow) : ℕ :=
  w.lowerScale + w.middleScale + w.upperScale + w.slack

theorem scaleSeparation_budget_le_certificate {w : ScaleSeparationWindow}
    (h : scaleSeparationWindowReady w) :
    w.separationBudget ≤ w.certificate := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleScaleSeparationWindow : ScaleSeparationWindow :=
  { lowerScale := 2, middleScale := 5, upperScale := 11, separationBudget := 17, slack := 0 }

example : scaleSeparationWindowReady sampleScaleSeparationWindow := by
  norm_num [scaleSeparationWindowReady, ScaleSeparationWindow.ordered,
    ScaleSeparationWindow.separationControlled, sampleScaleSeparationWindow]

example : sampleScaleSeparationWindow.certificate = 18 := by
  native_decide

/-- A refinement certificate for scale separation windows. -/
structure ScaleSeparationCertificate where
  lowerWindow : ℕ
  middleWindow : ℕ
  upperWindow : ℕ
  separationBudgetWindow : ℕ
  slack : ℕ

/-- Scale separation certificates keep ordered windows and bounded gaps. -/
def scaleSeparationCertificateControlled
    (w : ScaleSeparationCertificate) : Prop :=
  w.lowerWindow ≤ w.middleWindow ∧
    w.middleWindow ≤ w.upperWindow + w.slack ∧
      w.separationBudgetWindow ≤
        w.lowerWindow + w.middleWindow + w.upperWindow + w.slack

/-- Readiness for a scale separation certificate. -/
def scaleSeparationCertificateReady
    (w : ScaleSeparationCertificate) : Prop :=
  scaleSeparationCertificateControlled w ∧
    w.separationBudgetWindow ≤
      w.lowerWindow + w.middleWindow + w.upperWindow +
        w.separationBudgetWindow + w.slack

/-- Total size of a scale separation certificate. -/
def scaleSeparationCertificateSize
    (w : ScaleSeparationCertificate) : ℕ :=
  w.lowerWindow + w.middleWindow + w.upperWindow +
    w.separationBudgetWindow + w.slack

theorem scaleSeparationCertificate_budget_le_size
    (w : ScaleSeparationCertificate)
    (h : scaleSeparationCertificateReady w) :
    w.separationBudgetWindow ≤ scaleSeparationCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold scaleSeparationCertificateSize
  omega

def sampleScaleSeparationCertificate : ScaleSeparationCertificate where
  lowerWindow := 2
  middleWindow := 5
  upperWindow := 11
  separationBudgetWindow := 17
  slack := 0

example :
    scaleSeparationCertificateReady sampleScaleSeparationCertificate := by
  norm_num [scaleSeparationCertificateReady,
    scaleSeparationCertificateControlled, sampleScaleSeparationCertificate]

example :
    sampleScaleSeparationCertificate.separationBudgetWindow ≤
      scaleSeparationCertificateSize sampleScaleSeparationCertificate := by
  apply scaleSeparationCertificate_budget_le_size
  norm_num [scaleSeparationCertificateReady,
    scaleSeparationCertificateControlled, sampleScaleSeparationCertificate]

/-- A refinement certificate with the scale-separation budget separated from size. -/
structure ScaleSeparationRefinementCertificate where
  lowerWindow : ℕ
  middleWindow : ℕ
  upperWindow : ℕ
  separationBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ScaleSeparationRefinementCertificate.separationControlled
    (cert : ScaleSeparationRefinementCertificate) : Prop :=
  cert.lowerWindow ≤ cert.middleWindow ∧
    cert.middleWindow ≤ cert.upperWindow + cert.slack ∧
      cert.separationBudgetWindow ≤
        cert.lowerWindow + cert.middleWindow + cert.upperWindow + cert.slack

def ScaleSeparationRefinementCertificate.budgetControlled
    (cert : ScaleSeparationRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.lowerWindow + cert.middleWindow + cert.upperWindow +
      cert.separationBudgetWindow + cert.slack

def scaleSeparationRefinementReady
    (cert : ScaleSeparationRefinementCertificate) : Prop :=
  cert.separationControlled ∧ cert.budgetControlled

def ScaleSeparationRefinementCertificate.size
    (cert : ScaleSeparationRefinementCertificate) : ℕ :=
  cert.lowerWindow + cert.middleWindow + cert.upperWindow +
    cert.separationBudgetWindow + cert.slack

theorem scaleSeparation_certificateBudgetWindow_le_size
    (cert : ScaleSeparationRefinementCertificate)
    (h : scaleSeparationRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleScaleSeparationRefinementCertificate :
    ScaleSeparationRefinementCertificate :=
  { lowerWindow := 2, middleWindow := 5, upperWindow := 11,
    separationBudgetWindow := 17, certificateBudgetWindow := 35, slack := 0 }

example :
    scaleSeparationRefinementReady sampleScaleSeparationRefinementCertificate := by
  norm_num [scaleSeparationRefinementReady,
    ScaleSeparationRefinementCertificate.separationControlled,
    ScaleSeparationRefinementCertificate.budgetControlled,
    sampleScaleSeparationRefinementCertificate]

example :
    sampleScaleSeparationRefinementCertificate.certificateBudgetWindow ≤
      sampleScaleSeparationRefinementCertificate.size := by
  apply scaleSeparation_certificateBudgetWindow_le_size
  norm_num [scaleSeparationRefinementReady,
    ScaleSeparationRefinementCertificate.separationControlled,
    ScaleSeparationRefinementCertificate.budgetControlled,
    sampleScaleSeparationRefinementCertificate]


structure ScaleSeparationAlgebraBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ScaleSeparationAlgebraBudgetCertificate.controlled
    (c : ScaleSeparationAlgebraBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def ScaleSeparationAlgebraBudgetCertificate.budgetControlled
    (c : ScaleSeparationAlgebraBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ScaleSeparationAlgebraBudgetCertificate.Ready
    (c : ScaleSeparationAlgebraBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ScaleSeparationAlgebraBudgetCertificate.size
    (c : ScaleSeparationAlgebraBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem scaleSeparationAlgebra_budgetCertificate_le_size
    (c : ScaleSeparationAlgebraBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleScaleSeparationAlgebraBudgetCertificate :
    ScaleSeparationAlgebraBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleScaleSeparationAlgebraBudgetCertificate.Ready := by
  constructor
  · norm_num [ScaleSeparationAlgebraBudgetCertificate.controlled,
      sampleScaleSeparationAlgebraBudgetCertificate]
  · norm_num [ScaleSeparationAlgebraBudgetCertificate.budgetControlled,
      sampleScaleSeparationAlgebraBudgetCertificate]

example :
    sampleScaleSeparationAlgebraBudgetCertificate.certificateBudgetWindow ≤
      sampleScaleSeparationAlgebraBudgetCertificate.size := by
  apply scaleSeparationAlgebra_budgetCertificate_le_size
  constructor
  · norm_num [ScaleSeparationAlgebraBudgetCertificate.controlled,
      sampleScaleSeparationAlgebraBudgetCertificate]
  · norm_num [ScaleSeparationAlgebraBudgetCertificate.budgetControlled,
      sampleScaleSeparationAlgebraBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleScaleSeparationAlgebraBudgetCertificate.Ready := by
  constructor
  · norm_num [ScaleSeparationAlgebraBudgetCertificate.controlled,
      sampleScaleSeparationAlgebraBudgetCertificate]
  · norm_num [ScaleSeparationAlgebraBudgetCertificate.budgetControlled,
      sampleScaleSeparationAlgebraBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleScaleSeparationAlgebraBudgetCertificate.certificateBudgetWindow ≤
      sampleScaleSeparationAlgebraBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ScaleSeparationAlgebraBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleScaleSeparationAlgebraBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleScaleSeparationAlgebraBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.ScaleSeparationAlgebra
