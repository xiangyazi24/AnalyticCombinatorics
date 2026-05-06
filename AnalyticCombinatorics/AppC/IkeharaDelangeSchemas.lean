import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Ikehara-Delange Tauberian schema bookkeeping.

The data records pole order, residue positivity, and logarithmic correction
budgets.
-/

namespace AnalyticCombinatorics.AppC.IkeharaDelangeSchemas

structure IkeharaDelangeData where
  poleOrder : ℕ
  residuePositive : Prop
  logarithmicCorrection : ℕ
deriving Repr

def positivePoleOrder (d : IkeharaDelangeData) : Prop :=
  0 < d.poleOrder

def ikeharaDelangeReady (d : IkeharaDelangeData) : Prop :=
  positivePoleOrder d ∧ d.residuePositive

def ikeharaDelangeScale (d : IkeharaDelangeData) : ℕ :=
  d.poleOrder + d.logarithmicCorrection

theorem ikeharaDelangeReady.residue {d : IkeharaDelangeData}
    (h : ikeharaDelangeReady d) :
    d.residuePositive := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem poleOrder_le_scale {d : IkeharaDelangeData}
    (h : positivePoleOrder d) :
    positivePoleOrder d ∧ d.poleOrder ≤ ikeharaDelangeScale d := by
  refine ⟨h, ?_⟩
  unfold ikeharaDelangeScale
  omega

def sampleIkeharaDelange : IkeharaDelangeData :=
  { poleOrder := 3, residuePositive := 0 < 8, logarithmicCorrection := 5 }

example : ikeharaDelangeReady sampleIkeharaDelange := by
  norm_num [ikeharaDelangeReady, positivePoleOrder, sampleIkeharaDelange]

example : ikeharaDelangeScale sampleIkeharaDelange = 8 := by
  native_decide

structure IkeharaDelangeWindow where
  poleOrder : ℕ
  residueBudget : ℕ
  logarithmicCorrection : ℕ
  coefficientMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def IkeharaDelangeWindow.poleReady (w : IkeharaDelangeWindow) : Prop :=
  0 < w.poleOrder ∧ 0 < w.residueBudget

def IkeharaDelangeWindow.coefficientControlled (w : IkeharaDelangeWindow) : Prop :=
  w.coefficientMass ≤ w.residueBudget * (w.poleOrder + w.logarithmicCorrection) + w.slack

def IkeharaDelangeWindow.ready (w : IkeharaDelangeWindow) : Prop :=
  w.poleReady ∧ w.coefficientControlled

def IkeharaDelangeWindow.certificate (w : IkeharaDelangeWindow) : ℕ :=
  w.poleOrder + w.residueBudget + w.logarithmicCorrection + w.coefficientMass + w.slack

theorem residueBudget_le_certificate (w : IkeharaDelangeWindow) :
    w.residueBudget ≤ w.certificate := by
  unfold IkeharaDelangeWindow.certificate
  omega

def sampleIkeharaDelangeWindow : IkeharaDelangeWindow :=
  { poleOrder := 3, residueBudget := 8, logarithmicCorrection := 5,
    coefficientMass := 20, slack := 0 }

example : sampleIkeharaDelangeWindow.ready := by
  norm_num [sampleIkeharaDelangeWindow, IkeharaDelangeWindow.ready,
    IkeharaDelangeWindow.poleReady, IkeharaDelangeWindow.coefficientControlled]

structure IkeharaDelangeRefinementWindow where
  poleWindow : ℕ
  residueWindow : ℕ
  logarithmicWindow : ℕ
  coefficientWindow : ℕ
  delangeBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def IkeharaDelangeRefinementWindow.coefficientControlled
    (w : IkeharaDelangeRefinementWindow) : Prop :=
  w.coefficientWindow ≤ w.residueWindow * (w.poleWindow + w.logarithmicWindow) + w.slack

def ikeharaDelangeRefinementWindowReady
    (w : IkeharaDelangeRefinementWindow) : Prop :=
  0 < w.poleWindow ∧ 0 < w.residueWindow ∧ w.coefficientControlled ∧
    w.delangeBudget ≤ w.poleWindow + w.residueWindow + w.coefficientWindow + w.slack

def IkeharaDelangeRefinementWindow.certificate
    (w : IkeharaDelangeRefinementWindow) : ℕ :=
  w.poleWindow + w.residueWindow + w.logarithmicWindow + w.coefficientWindow +
    w.delangeBudget + w.slack

theorem ikeharaDelangeRefinement_budget_le_certificate
    (w : IkeharaDelangeRefinementWindow) :
    w.delangeBudget ≤ w.certificate := by
  unfold IkeharaDelangeRefinementWindow.certificate
  omega

def sampleIkeharaDelangeRefinementWindow :
    IkeharaDelangeRefinementWindow :=
  { poleWindow := 3, residueWindow := 8, logarithmicWindow := 5,
    coefficientWindow := 20, delangeBudget := 32, slack := 1 }

example : ikeharaDelangeRefinementWindowReady
    sampleIkeharaDelangeRefinementWindow := by
  norm_num [ikeharaDelangeRefinementWindowReady,
    IkeharaDelangeRefinementWindow.coefficientControlled,
    sampleIkeharaDelangeRefinementWindow]


structure IkeharaDelangeSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def IkeharaDelangeSchemasBudgetCertificate.controlled
    (c : IkeharaDelangeSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def IkeharaDelangeSchemasBudgetCertificate.budgetControlled
    (c : IkeharaDelangeSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def IkeharaDelangeSchemasBudgetCertificate.Ready
    (c : IkeharaDelangeSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def IkeharaDelangeSchemasBudgetCertificate.size
    (c : IkeharaDelangeSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem ikeharaDelangeSchemas_budgetCertificate_le_size
    (c : IkeharaDelangeSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleIkeharaDelangeSchemasBudgetCertificate :
    IkeharaDelangeSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleIkeharaDelangeSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [IkeharaDelangeSchemasBudgetCertificate.controlled,
      sampleIkeharaDelangeSchemasBudgetCertificate]
  · norm_num [IkeharaDelangeSchemasBudgetCertificate.budgetControlled,
      sampleIkeharaDelangeSchemasBudgetCertificate]

example :
    sampleIkeharaDelangeSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleIkeharaDelangeSchemasBudgetCertificate.size := by
  apply ikeharaDelangeSchemas_budgetCertificate_le_size
  constructor
  · norm_num [IkeharaDelangeSchemasBudgetCertificate.controlled,
      sampleIkeharaDelangeSchemasBudgetCertificate]
  · norm_num [IkeharaDelangeSchemasBudgetCertificate.budgetControlled,
      sampleIkeharaDelangeSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleIkeharaDelangeSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [IkeharaDelangeSchemasBudgetCertificate.controlled,
      sampleIkeharaDelangeSchemasBudgetCertificate]
  · norm_num [IkeharaDelangeSchemasBudgetCertificate.budgetControlled,
      sampleIkeharaDelangeSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleIkeharaDelangeSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleIkeharaDelangeSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List IkeharaDelangeSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleIkeharaDelangeSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleIkeharaDelangeSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.IkeharaDelangeSchemas
