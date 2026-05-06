import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Tightness criterion bookkeeping.

The file records compact mass and tail budget checks for probability limit
schemas.
-/

namespace AnalyticCombinatorics.AppC.TightnessCriteriaSchemas

structure TightnessDatum where
  compactMass : ℕ
  tailMass : ℕ
  totalMass : ℕ
deriving DecidableEq, Repr

def massDecomposes (d : TightnessDatum) : Prop :=
  d.compactMass + d.tailMass = d.totalMass

def tailControlled (d : TightnessDatum) (budget : ℕ) : Prop :=
  d.tailMass ≤ budget

def tightnessReady (d : TightnessDatum) (budget : ℕ) : Prop :=
  massDecomposes d ∧ tailControlled d budget

theorem tightnessReady.tail {d : TightnessDatum} {budget : ℕ}
    (h : tightnessReady d budget) :
    tailControlled d budget := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem massDecomposes.compact_le {d : TightnessDatum}
    (h : massDecomposes d) :
    d.compactMass ≤ d.totalMass := by
  unfold massDecomposes at h
  omega

def sampleTightness : TightnessDatum :=
  { compactMass := 8, tailMass := 2, totalMass := 10 }

example : tightnessReady sampleTightness 3 := by
  norm_num [tightnessReady, massDecomposes, tailControlled, sampleTightness]

example : tailControlled sampleTightness 2 := by
  norm_num [tailControlled, sampleTightness]

structure TightnessWindow where
  compactMass : ℕ
  tailMass : ℕ
  totalMass : ℕ
  tailBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TightnessWindow.massControlled (w : TightnessWindow) : Prop :=
  w.compactMass + w.tailMass ≤ w.totalMass + w.slack

def TightnessWindow.tailControlled (w : TightnessWindow) : Prop :=
  w.tailMass ≤ w.tailBudget + w.slack

def TightnessWindow.ready (w : TightnessWindow) : Prop :=
  w.massControlled ∧ w.tailControlled

def TightnessWindow.certificate (w : TightnessWindow) : ℕ :=
  w.compactMass + w.tailMass + w.totalMass + w.tailBudget + w.slack

theorem totalMass_le_certificate (w : TightnessWindow) :
    w.totalMass ≤ w.certificate := by
  unfold TightnessWindow.certificate
  omega

def sampleTightnessWindow : TightnessWindow :=
  { compactMass := 8, tailMass := 2, totalMass := 10, tailBudget := 3, slack := 0 }

example : sampleTightnessWindow.ready := by
  norm_num [sampleTightnessWindow, TightnessWindow.ready,
    TightnessWindow.massControlled, TightnessWindow.tailControlled]

structure TightnessRefinementWindow where
  compactWindow : ℕ
  tailWindow : ℕ
  totalWindow : ℕ
  tightnessBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TightnessRefinementWindow.massControlled
    (w : TightnessRefinementWindow) : Prop :=
  w.compactWindow + w.tailWindow ≤ w.totalWindow + w.slack

def tightnessRefinementWindowReady (w : TightnessRefinementWindow) : Prop :=
  w.massControlled ∧
    w.tightnessBudget ≤ w.compactWindow + w.tailWindow + w.totalWindow + w.slack

def TightnessRefinementWindow.certificate
    (w : TightnessRefinementWindow) : ℕ :=
  w.compactWindow + w.tailWindow + w.totalWindow + w.tightnessBudget + w.slack

theorem tightnessRefinement_budget_le_certificate
    (w : TightnessRefinementWindow) :
    w.tightnessBudget ≤ w.certificate := by
  unfold TightnessRefinementWindow.certificate
  omega

def sampleTightnessRefinementWindow : TightnessRefinementWindow :=
  { compactWindow := 8, tailWindow := 2, totalWindow := 10,
    tightnessBudget := 21, slack := 1 }

example : tightnessRefinementWindowReady sampleTightnessRefinementWindow := by
  norm_num [tightnessRefinementWindowReady,
    TightnessRefinementWindow.massControlled, sampleTightnessRefinementWindow]


structure TightnessCriteriaSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TightnessCriteriaSchemasBudgetCertificate.controlled
    (c : TightnessCriteriaSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TightnessCriteriaSchemasBudgetCertificate.budgetControlled
    (c : TightnessCriteriaSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TightnessCriteriaSchemasBudgetCertificate.Ready
    (c : TightnessCriteriaSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TightnessCriteriaSchemasBudgetCertificate.size
    (c : TightnessCriteriaSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem tightnessCriteriaSchemas_budgetCertificate_le_size
    (c : TightnessCriteriaSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTightnessCriteriaSchemasBudgetCertificate :
    TightnessCriteriaSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleTightnessCriteriaSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TightnessCriteriaSchemasBudgetCertificate.controlled,
      sampleTightnessCriteriaSchemasBudgetCertificate]
  · norm_num [TightnessCriteriaSchemasBudgetCertificate.budgetControlled,
      sampleTightnessCriteriaSchemasBudgetCertificate]

example :
    sampleTightnessCriteriaSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTightnessCriteriaSchemasBudgetCertificate.size := by
  apply tightnessCriteriaSchemas_budgetCertificate_le_size
  constructor
  · norm_num [TightnessCriteriaSchemasBudgetCertificate.controlled,
      sampleTightnessCriteriaSchemasBudgetCertificate]
  · norm_num [TightnessCriteriaSchemasBudgetCertificate.budgetControlled,
      sampleTightnessCriteriaSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTightnessCriteriaSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TightnessCriteriaSchemasBudgetCertificate.controlled,
      sampleTightnessCriteriaSchemasBudgetCertificate]
  · norm_num [TightnessCriteriaSchemasBudgetCertificate.budgetControlled,
      sampleTightnessCriteriaSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTightnessCriteriaSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTightnessCriteriaSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List TightnessCriteriaSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTightnessCriteriaSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTightnessCriteriaSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.TightnessCriteriaSchemas
