import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Prokhorov-type compactness schema bookkeeping.

The finite data records tightness radius, compact-cover count, and error
budget.
-/

namespace AnalyticCombinatorics.AppC.ProkhorovSchemas

structure ProkhorovData where
  tightnessRadius : ℕ
  compactCoverCount : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def positiveTightnessRadius (d : ProkhorovData) : Prop :=
  0 < d.tightnessRadius

def nonemptyCompactCover (d : ProkhorovData) : Prop :=
  0 < d.compactCoverCount

def prokhorovReady (d : ProkhorovData) : Prop :=
  positiveTightnessRadius d ∧ nonemptyCompactCover d

def prokhorovBudget (d : ProkhorovData) : ℕ :=
  d.tightnessRadius + d.compactCoverCount + d.errorBudget

theorem prokhorovReady.radius {d : ProkhorovData}
    (h : prokhorovReady d) :
    positiveTightnessRadius d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem tightnessRadius_le_budget (d : ProkhorovData) :
    d.tightnessRadius ≤ prokhorovBudget d := by
  unfold prokhorovBudget
  omega

def sampleProkhorov : ProkhorovData :=
  { tightnessRadius := 5, compactCoverCount := 4, errorBudget := 2 }

example : prokhorovReady sampleProkhorov := by
  norm_num [prokhorovReady, positiveTightnessRadius, nonemptyCompactCover, sampleProkhorov]

example : prokhorovBudget sampleProkhorov = 11 := by
  native_decide

structure ProkhorovWindow where
  tightnessRadius : ℕ
  compactCoverCount : ℕ
  errorBudget : ℕ
  measureMass : ℕ
deriving DecidableEq, Repr

def ProkhorovWindow.compactReady (w : ProkhorovWindow) : Prop :=
  0 < w.tightnessRadius ∧ 0 < w.compactCoverCount

def ProkhorovWindow.errorControlled (w : ProkhorovWindow) : Prop :=
  w.errorBudget ≤ w.tightnessRadius + w.compactCoverCount

def ProkhorovWindow.massControlled (w : ProkhorovWindow) : Prop :=
  w.measureMass ≤ w.tightnessRadius + w.compactCoverCount + w.errorBudget

def ProkhorovWindow.ready (w : ProkhorovWindow) : Prop :=
  w.compactReady ∧ w.errorControlled ∧ w.massControlled

def ProkhorovWindow.certificate (w : ProkhorovWindow) : ℕ :=
  w.tightnessRadius + w.compactCoverCount + w.errorBudget + w.measureMass

theorem measureMass_le_certificate (w : ProkhorovWindow) :
    w.measureMass ≤ w.certificate := by
  unfold ProkhorovWindow.certificate
  omega

def sampleProkhorovWindow : ProkhorovWindow :=
  { tightnessRadius := 5, compactCoverCount := 4, errorBudget := 2, measureMass := 8 }

example : sampleProkhorovWindow.ready := by
  norm_num [sampleProkhorovWindow, ProkhorovWindow.ready, ProkhorovWindow.compactReady,
    ProkhorovWindow.errorControlled, ProkhorovWindow.massControlled]

structure ProkhorovRefinementWindow where
  radiusWindow : ℕ
  coverWindow : ℕ
  errorWindow : ℕ
  massWindow : ℕ
  prokhorovBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProkhorovRefinementWindow.massControlled
    (w : ProkhorovRefinementWindow) : Prop :=
  w.massWindow ≤ w.radiusWindow + w.coverWindow + w.errorWindow + w.slack

def prokhorovRefinementWindowReady
    (w : ProkhorovRefinementWindow) : Prop :=
  0 < w.radiusWindow ∧ 0 < w.coverWindow ∧ w.massControlled ∧
    w.prokhorovBudget ≤ w.radiusWindow + w.coverWindow + w.massWindow + w.slack

def ProkhorovRefinementWindow.certificate
    (w : ProkhorovRefinementWindow) : ℕ :=
  w.radiusWindow + w.coverWindow + w.errorWindow + w.massWindow + w.prokhorovBudget + w.slack

theorem prokhorovRefinement_budget_le_certificate
    (w : ProkhorovRefinementWindow) :
    w.prokhorovBudget ≤ w.certificate := by
  unfold ProkhorovRefinementWindow.certificate
  omega

def sampleProkhorovRefinementWindow : ProkhorovRefinementWindow :=
  { radiusWindow := 5, coverWindow := 4, errorWindow := 2, massWindow := 8,
    prokhorovBudget := 18, slack := 1 }

example : prokhorovRefinementWindowReady sampleProkhorovRefinementWindow := by
  norm_num [prokhorovRefinementWindowReady,
    ProkhorovRefinementWindow.massControlled, sampleProkhorovRefinementWindow]


structure ProkhorovSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProkhorovSchemasBudgetCertificate.controlled
    (c : ProkhorovSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ProkhorovSchemasBudgetCertificate.budgetControlled
    (c : ProkhorovSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ProkhorovSchemasBudgetCertificate.Ready
    (c : ProkhorovSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ProkhorovSchemasBudgetCertificate.size
    (c : ProkhorovSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem prokhorovSchemas_budgetCertificate_le_size
    (c : ProkhorovSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleProkhorovSchemasBudgetCertificate :
    ProkhorovSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleProkhorovSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ProkhorovSchemasBudgetCertificate.controlled,
      sampleProkhorovSchemasBudgetCertificate]
  · norm_num [ProkhorovSchemasBudgetCertificate.budgetControlled,
      sampleProkhorovSchemasBudgetCertificate]

example :
    sampleProkhorovSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleProkhorovSchemasBudgetCertificate.size := by
  apply prokhorovSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ProkhorovSchemasBudgetCertificate.controlled,
      sampleProkhorovSchemasBudgetCertificate]
  · norm_num [ProkhorovSchemasBudgetCertificate.budgetControlled,
      sampleProkhorovSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleProkhorovSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ProkhorovSchemasBudgetCertificate.controlled,
      sampleProkhorovSchemasBudgetCertificate]
  · norm_num [ProkhorovSchemasBudgetCertificate.budgetControlled,
      sampleProkhorovSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleProkhorovSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleProkhorovSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ProkhorovSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleProkhorovSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleProkhorovSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ProkhorovSchemas
