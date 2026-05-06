import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Newton polygon asymptotics
-/

namespace AnalyticCombinatorics.Asymptotics.NewtonPolygonAsymptotics

/-- A Newton polygon edge with integer endpoint coordinates. -/
structure NewtonEdge where
  x0 : ℕ
  y0 : ℕ
  x1 : ℕ
  y1 : ℕ
deriving DecidableEq, Repr

def NewtonEdge.horizontalSpan (e : NewtonEdge) : ℕ :=
  e.x1 - e.x0

def NewtonEdge.verticalDrop (e : NewtonEdge) : ℕ :=
  e.y0 - e.y1

def NewtonEdge.ready (e : NewtonEdge) : Prop :=
  e.x0 < e.x1 ∧ e.y1 ≤ e.y0

def sampleNewtonEdge : NewtonEdge :=
  { x0 := 0, y0 := 3, x1 := 2, y1 := 1 }

theorem sampleNewtonEdge_ready :
    sampleNewtonEdge.ready := by
  norm_num [NewtonEdge.ready, sampleNewtonEdge]

theorem sampleNewtonEdge_slope_data :
    sampleNewtonEdge.horizontalSpan = 2 ∧
      sampleNewtonEdge.verticalDrop = 2 := by
  native_decide

/-- Cleared-denominator slope data for Newton polygon transfer. -/
def slopeNumeratorDenominator (e : NewtonEdge) : ℕ × ℕ :=
  (e.verticalDrop, e.horizontalSpan)

theorem slopeNumeratorDenominator_sample :
    slopeNumeratorDenominator sampleNewtonEdge = (2, 2) := by
  native_decide

structure NewtonPolygonWindow where
  edgeWindow : ℕ
  slopeWindow : ℕ
  expansionWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def NewtonPolygonWindow.ready (w : NewtonPolygonWindow) : Prop :=
  0 < w.edgeWindow ∧
    w.expansionWindow ≤ w.edgeWindow + w.slopeWindow + w.slack

def sampleNewtonPolygonWindow : NewtonPolygonWindow :=
  { edgeWindow := 4, slopeWindow := 3, expansionWindow := 7, slack := 0 }

example : sampleNewtonPolygonWindow.ready := by
  norm_num [NewtonPolygonWindow.ready, sampleNewtonPolygonWindow]

structure BudgetCertificate where
  polygonWindow : ℕ
  expansionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.polygonWindow ∧ c.expansionWindow ≤ c.polygonWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.polygonWindow + c.expansionWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.polygonWindow + c.expansionWindow + c.slack

theorem newtonPolygonAsymptotics_budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { polygonWindow := 5, expansionWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.NewtonPolygonAsymptotics
