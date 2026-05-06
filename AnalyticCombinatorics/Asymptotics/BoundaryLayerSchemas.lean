import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Boundary-layer bookkeeping for uniform asymptotics.

The finite data separates interior estimates from the boundary strip where a
different scale is used.
-/

namespace AnalyticCombinatorics.Asymptotics.BoundaryLayerSchemas

structure BoundaryLayerData where
  interiorWidth : ℕ
  boundaryWidth : ℕ
  matchingError : ℕ
deriving DecidableEq, Repr

def nontrivialLayer (d : BoundaryLayerData) : Prop :=
  0 < d.interiorWidth ∧ 0 < d.boundaryWidth

def matchedLayer (d : BoundaryLayerData) : Prop :=
  nontrivialLayer d ∧ d.matchingError ≤ d.interiorWidth + d.boundaryWidth

def totalWidth (d : BoundaryLayerData) : ℕ :=
  d.interiorWidth + d.boundaryWidth

theorem matchedLayer.nontrivial {d : BoundaryLayerData}
    (h : matchedLayer d) :
    nontrivialLayer d ∧ d.matchingError ≤ d.interiorWidth + d.boundaryWidth ∧
      0 < totalWidth d := by
  refine ⟨h.1, h.2, ?_⟩
  rcases h.1 with ⟨hinterior, hboundary⟩
  unfold totalWidth
  omega

theorem totalWidth_positive {d : BoundaryLayerData}
    (h : nontrivialLayer d) :
    0 < totalWidth d := by
  unfold nontrivialLayer totalWidth at *
  omega

def sampleLayer : BoundaryLayerData :=
  { interiorWidth := 6, boundaryWidth := 2, matchingError := 3 }

example : matchedLayer sampleLayer := by
  norm_num [matchedLayer, nontrivialLayer, sampleLayer]

example : totalWidth sampleLayer = 8 := by
  native_decide

/-- Finite executable readiness audit for boundary-layer data. -/
def boundaryLayerDataListReady
    (data : List BoundaryLayerData) : Bool :=
  data.all fun d =>
    0 < d.interiorWidth &&
      0 < d.boundaryWidth &&
        d.matchingError ≤ d.interiorWidth + d.boundaryWidth

theorem boundaryLayerDataList_readyWindow :
    boundaryLayerDataListReady
      [{ interiorWidth := 4, boundaryWidth := 1, matchingError := 2 },
       { interiorWidth := 6, boundaryWidth := 2, matchingError := 3 }] = true := by
  unfold boundaryLayerDataListReady
  native_decide

structure BoundaryLayerWindow where
  interiorWidth : ℕ
  boundaryWidth : ℕ
  matchingError : ℕ
  overlapBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundaryLayerWindow.matchingControlled (w : BoundaryLayerWindow) : Prop :=
  w.matchingError ≤ w.interiorWidth + w.boundaryWidth + w.slack

def BoundaryLayerWindow.overlapControlled (w : BoundaryLayerWindow) : Prop :=
  w.overlapBudget ≤ w.interiorWidth + w.boundaryWidth + w.matchingError + w.slack

def boundaryLayerWindowReady (w : BoundaryLayerWindow) : Prop :=
  0 < w.interiorWidth ∧
    0 < w.boundaryWidth ∧
    w.matchingControlled ∧
    w.overlapControlled

def BoundaryLayerWindow.certificate (w : BoundaryLayerWindow) : ℕ :=
  w.interiorWidth + w.boundaryWidth + w.matchingError + w.slack

theorem boundaryLayer_overlapBudget_le_certificate {w : BoundaryLayerWindow}
    (h : boundaryLayerWindowReady w) :
    w.overlapBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hoverlap⟩
  exact hoverlap

def sampleBoundaryLayerWindow : BoundaryLayerWindow :=
  { interiorWidth := 6, boundaryWidth := 2, matchingError := 3, overlapBudget := 10,
    slack := 0 }

example : boundaryLayerWindowReady sampleBoundaryLayerWindow := by
  norm_num [boundaryLayerWindowReady, BoundaryLayerWindow.matchingControlled,
    BoundaryLayerWindow.overlapControlled, sampleBoundaryLayerWindow]

example : sampleBoundaryLayerWindow.certificate = 11 := by
  native_decide

structure BoundaryLayerCertificate where
  interiorWindow : ℕ
  boundaryWindow : ℕ
  matchingWindow : ℕ
  overlapWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundaryLayerCertificate.matchingControlled
    (c : BoundaryLayerCertificate) : Prop :=
  c.matchingWindow ≤ c.interiorWindow + c.boundaryWindow + c.slack

def BoundaryLayerCertificate.overlapControlled
    (c : BoundaryLayerCertificate) : Prop :=
  c.overlapWindow ≤
    c.interiorWindow + c.boundaryWindow + c.matchingWindow + c.slack

def boundaryLayerCertificateReady
    (c : BoundaryLayerCertificate) : Prop :=
  0 < c.interiorWindow ∧
    0 < c.boundaryWindow ∧
    c.matchingControlled ∧
    c.overlapControlled

def BoundaryLayerCertificate.size
    (c : BoundaryLayerCertificate) : ℕ :=
  c.interiorWindow + c.boundaryWindow + c.matchingWindow + c.slack

theorem boundaryLayer_overlapWindow_le_size
    {c : BoundaryLayerCertificate}
    (h : boundaryLayerCertificateReady c) :
    c.overlapWindow ≤ c.size := by
  rcases h with ⟨_, _, _, hoverlap⟩
  exact hoverlap

def sampleBoundaryLayerCertificate : BoundaryLayerCertificate :=
  { interiorWindow := 6, boundaryWindow := 2, matchingWindow := 3,
    overlapWindow := 10, slack := 0 }

example : boundaryLayerCertificateReady sampleBoundaryLayerCertificate := by
  norm_num [boundaryLayerCertificateReady,
    BoundaryLayerCertificate.matchingControlled,
    BoundaryLayerCertificate.overlapControlled,
    sampleBoundaryLayerCertificate]

example :
    sampleBoundaryLayerCertificate.overlapWindow ≤
      sampleBoundaryLayerCertificate.size := by
  norm_num [BoundaryLayerCertificate.size, sampleBoundaryLayerCertificate]

/-- A refinement certificate with the boundary-layer budget separated from size. -/
structure BoundaryLayerRefinementCertificate where
  interiorWindow : ℕ
  boundaryWindow : ℕ
  matchingWindow : ℕ
  overlapWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundaryLayerRefinementCertificate.layerControlled
    (cert : BoundaryLayerRefinementCertificate) : Prop :=
  0 < cert.interiorWindow ∧
    0 < cert.boundaryWindow ∧
      cert.matchingWindow ≤ cert.interiorWindow + cert.boundaryWindow + cert.slack ∧
        cert.overlapWindow ≤
          cert.interiorWindow + cert.boundaryWindow + cert.matchingWindow + cert.slack

def BoundaryLayerRefinementCertificate.budgetControlled
    (cert : BoundaryLayerRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.interiorWindow + cert.boundaryWindow + cert.matchingWindow +
      cert.overlapWindow + cert.slack

def boundaryLayerRefinementReady
    (cert : BoundaryLayerRefinementCertificate) : Prop :=
  cert.layerControlled ∧ cert.budgetControlled

def BoundaryLayerRefinementCertificate.size
    (cert : BoundaryLayerRefinementCertificate) : ℕ :=
  cert.interiorWindow + cert.boundaryWindow + cert.matchingWindow +
    cert.overlapWindow + cert.slack

theorem boundaryLayer_certificateBudgetWindow_le_size
    (cert : BoundaryLayerRefinementCertificate)
    (h : boundaryLayerRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBoundaryLayerRefinementCertificate :
    BoundaryLayerRefinementCertificate :=
  { interiorWindow := 6, boundaryWindow := 2, matchingWindow := 3,
    overlapWindow := 10, certificateBudgetWindow := 21, slack := 0 }

example :
    boundaryLayerRefinementReady sampleBoundaryLayerRefinementCertificate := by
  norm_num [boundaryLayerRefinementReady,
    BoundaryLayerRefinementCertificate.layerControlled,
    BoundaryLayerRefinementCertificate.budgetControlled,
    sampleBoundaryLayerRefinementCertificate]

example :
    sampleBoundaryLayerRefinementCertificate.certificateBudgetWindow ≤
      sampleBoundaryLayerRefinementCertificate.size := by
  apply boundaryLayer_certificateBudgetWindow_le_size
  norm_num [boundaryLayerRefinementReady,
    BoundaryLayerRefinementCertificate.layerControlled,
    BoundaryLayerRefinementCertificate.budgetControlled,
    sampleBoundaryLayerRefinementCertificate]


structure BoundaryLayerSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundaryLayerSchemasBudgetCertificate.controlled
    (c : BoundaryLayerSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def BoundaryLayerSchemasBudgetCertificate.budgetControlled
    (c : BoundaryLayerSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BoundaryLayerSchemasBudgetCertificate.Ready
    (c : BoundaryLayerSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BoundaryLayerSchemasBudgetCertificate.size
    (c : BoundaryLayerSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem boundaryLayerSchemas_budgetCertificate_le_size
    (c : BoundaryLayerSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBoundaryLayerSchemasBudgetCertificate :
    BoundaryLayerSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleBoundaryLayerSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundaryLayerSchemasBudgetCertificate.controlled,
      sampleBoundaryLayerSchemasBudgetCertificate]
  · norm_num [BoundaryLayerSchemasBudgetCertificate.budgetControlled,
      sampleBoundaryLayerSchemasBudgetCertificate]

example :
    sampleBoundaryLayerSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundaryLayerSchemasBudgetCertificate.size := by
  apply boundaryLayerSchemas_budgetCertificate_le_size
  constructor
  · norm_num [BoundaryLayerSchemasBudgetCertificate.controlled,
      sampleBoundaryLayerSchemasBudgetCertificate]
  · norm_num [BoundaryLayerSchemasBudgetCertificate.budgetControlled,
      sampleBoundaryLayerSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBoundaryLayerSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundaryLayerSchemasBudgetCertificate.controlled,
      sampleBoundaryLayerSchemasBudgetCertificate]
  · norm_num [BoundaryLayerSchemasBudgetCertificate.budgetControlled,
      sampleBoundaryLayerSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBoundaryLayerSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundaryLayerSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List BoundaryLayerSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBoundaryLayerSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleBoundaryLayerSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.BoundaryLayerSchemas
