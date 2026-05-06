import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Winding number models.

The finite abstraction records loop pieces, target separation, and
variation budgets.
-/

namespace AnalyticCombinatorics.AppB.WindingNumberModels

structure WindingNumberData where
  loopPieces : ℕ
  targetSeparation : ℕ
  variationBudget : ℕ
deriving DecidableEq, Repr

def separatedTarget (d : WindingNumberData) : Prop :=
  0 < d.targetSeparation

def variationControlled (d : WindingNumberData) : Prop :=
  d.variationBudget ≤ d.loopPieces + d.targetSeparation

def windingNumberReady (d : WindingNumberData) : Prop :=
  separatedTarget d ∧ variationControlled d

def windingNumberBudget (d : WindingNumberData) : ℕ :=
  d.loopPieces + d.targetSeparation + d.variationBudget

theorem windingNumberReady.separation {d : WindingNumberData}
    (h : windingNumberReady d) :
    separatedTarget d ∧ variationControlled d ∧
      d.loopPieces ≤ windingNumberBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold windingNumberBudget
  omega

theorem loopPieces_le_windingBudget (d : WindingNumberData) :
    d.loopPieces ≤ windingNumberBudget d := by
  unfold windingNumberBudget
  omega

def sampleWindingNumberData : WindingNumberData :=
  { loopPieces := 7, targetSeparation := 3, variationBudget := 8 }

example : windingNumberReady sampleWindingNumberData := by
  norm_num [windingNumberReady, separatedTarget]
  norm_num [variationControlled, sampleWindingNumberData]

example : windingNumberBudget sampleWindingNumberData = 18 := by
  native_decide

/-- Finite executable readiness audit for winding-number windows. -/
def windingNumberListReady (windows : List WindingNumberData) : Bool :=
  windows.all fun d =>
    0 < d.targetSeparation && d.variationBudget ≤ d.loopPieces + d.targetSeparation

theorem windingNumberList_readyWindow :
    windingNumberListReady
      [{ loopPieces := 4, targetSeparation := 2, variationBudget := 5 },
       { loopPieces := 7, targetSeparation := 3, variationBudget := 8 }] = true := by
  unfold windingNumberListReady
  native_decide


structure WindingNumberModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WindingNumberModelsBudgetCertificate.controlled
    (c : WindingNumberModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def WindingNumberModelsBudgetCertificate.budgetControlled
    (c : WindingNumberModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def WindingNumberModelsBudgetCertificate.Ready
    (c : WindingNumberModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WindingNumberModelsBudgetCertificate.size
    (c : WindingNumberModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem windingNumberModels_budgetCertificate_le_size
    (c : WindingNumberModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWindingNumberModelsBudgetCertificate :
    WindingNumberModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleWindingNumberModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [WindingNumberModelsBudgetCertificate.controlled,
      sampleWindingNumberModelsBudgetCertificate]
  · norm_num [WindingNumberModelsBudgetCertificate.budgetControlled,
      sampleWindingNumberModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWindingNumberModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleWindingNumberModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleWindingNumberModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [WindingNumberModelsBudgetCertificate.controlled,
      sampleWindingNumberModelsBudgetCertificate]
  · norm_num [WindingNumberModelsBudgetCertificate.budgetControlled,
      sampleWindingNumberModelsBudgetCertificate]

example :
    sampleWindingNumberModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleWindingNumberModelsBudgetCertificate.size := by
  apply windingNumberModels_budgetCertificate_le_size
  constructor
  · norm_num [WindingNumberModelsBudgetCertificate.controlled,
      sampleWindingNumberModelsBudgetCertificate]
  · norm_num [WindingNumberModelsBudgetCertificate.budgetControlled,
      sampleWindingNumberModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List WindingNumberModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleWindingNumberModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleWindingNumberModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.WindingNumberModels
