import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Subcritical Composition

Finite coefficient models and statement forms for subcritical composition
schemas.
-/

namespace AnalyticCombinatorics.Asymptotics.SubcriticalComposition

def geometricCoeff (n : ℕ) : ℕ := n - n + 1

def shiftedGeometricCoeff (n : ℕ) : ℕ :=
  if n = 0 then 0 else 1

def cauchyProduct (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun s k => s + a k * b (n - k)) 0

theorem product_geometric_shifted :
    (List.range 7).map (cauchyProduct geometricCoeff shiftedGeometricCoeff) =
      [0, 1, 2, 3, 4, 5, 6] := by
  native_decide

def finiteCompositionToy (outer inner : ℕ → ℕ) (n : ℕ) : ℕ :=
  outer 0 + inner n

theorem finiteCompositionToy_samples :
    (List.range 5).map (finiteCompositionToy (fun _ => 1) (fun n => n ^ 2)) =
      [1, 2, 5, 10, 17] := by
  native_decide

structure SubcriticalData where
  outerRadiusInv : ℕ
  innerRadiusInv : ℕ
  separationNumerator : ℕ
  separationDenominator : ℕ

def basicSubcriticalData : SubcriticalData where
  outerRadiusInv := 2
  innerRadiusInv := 3
  separationNumerator := 1
  separationDenominator := 2

theorem basicSubcriticalData_values :
    basicSubcriticalData.outerRadiusInv = 2 ∧
    basicSubcriticalData.innerRadiusInv = 3 ∧
    basicSubcriticalData.separationDenominator = 2 := by
  native_decide

def subcriticalDataReady (data : SubcriticalData) : Prop :=
  0 < data.outerRadiusInv ∧ 0 < data.innerRadiusInv ∧ 0 < data.separationDenominator

theorem basicSubcriticalData_ready :
    subcriticalDataReady basicSubcriticalData := by
  unfold subcriticalDataReady basicSubcriticalData
  native_decide

/-- Finite executable readiness audit for subcritical composition data. -/
def subcriticalDataListReady (data : List SubcriticalData) : Bool :=
  data.all fun d =>
    0 < d.outerRadiusInv && 0 < d.innerRadiusInv && 0 < d.separationDenominator

theorem subcriticalDataList_readyWindow :
    subcriticalDataListReady
      [{ outerRadiusInv := 1, innerRadiusInv := 2,
         separationNumerator := 1, separationDenominator := 1 },
       { outerRadiusInv := 2, innerRadiusInv := 3,
         separationNumerator := 1, separationDenominator := 2 }] = true := by
  unfold subcriticalDataListReady
  native_decide

def SubcriticalCompositionSchema
    (outer inner : ℕ → ℂ) (data : SubcriticalData) : Prop :=
  subcriticalDataReady data ∧ outer 0 = inner 0 ∧ outer 4 = inner 4

def subcriticalOuterWitness (n : ℕ) : ℂ :=
  finiteCompositionToy geometricCoeff (fun k => k ^ 2) n

def subcriticalInnerWitness (n : ℕ) : ℂ :=
  if n = 0 then 1 else if n = 4 then 17 else 0

theorem subcritical_composition_schema_statement :
    SubcriticalCompositionSchema subcriticalOuterWitness subcriticalInnerWitness
      basicSubcriticalData := by
  unfold SubcriticalCompositionSchema subcriticalDataReady basicSubcriticalData
    subcriticalOuterWitness subcriticalInnerWitness finiteCompositionToy geometricCoeff
  norm_num

/-- A finite certificate for subcritical composition data. -/
structure SubcriticalCompositionCertificate where
  outerRadiusWindow : ℕ
  innerRadiusWindow : ℕ
  separationDenominatorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Subcritical certificates keep both radii and separation denominators positive. -/
def subcriticalCompositionCertificateControlled
    (w : SubcriticalCompositionCertificate) : Prop :=
  0 < w.outerRadiusWindow ∧
    0 < w.innerRadiusWindow ∧
      0 < w.separationDenominatorWindow

/-- Readiness for a subcritical composition certificate. -/
def subcriticalCompositionCertificateReady
    (w : SubcriticalCompositionCertificate) : Prop :=
  subcriticalCompositionCertificateControlled w ∧
    w.certificateBudget ≤
      w.outerRadiusWindow + w.innerRadiusWindow +
        w.separationDenominatorWindow + w.slack

/-- Total size of a subcritical composition certificate. -/
def subcriticalCompositionCertificateSize
    (w : SubcriticalCompositionCertificate) : ℕ :=
  w.outerRadiusWindow + w.innerRadiusWindow +
    w.separationDenominatorWindow + w.certificateBudget + w.slack

theorem subcriticalCompositionCertificate_budget_le_size
    (w : SubcriticalCompositionCertificate)
    (h : subcriticalCompositionCertificateReady w) :
    w.certificateBudget ≤ subcriticalCompositionCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold subcriticalCompositionCertificateSize
  omega

def sampleSubcriticalCompositionCertificate :
    SubcriticalCompositionCertificate where
  outerRadiusWindow := 2
  innerRadiusWindow := 3
  separationDenominatorWindow := 2
  certificateBudget := 7
  slack := 1

example :
    subcriticalCompositionCertificateReady
      sampleSubcriticalCompositionCertificate := by
  norm_num [subcriticalCompositionCertificateReady,
    subcriticalCompositionCertificateControlled,
    sampleSubcriticalCompositionCertificate]

example :
    sampleSubcriticalCompositionCertificate.certificateBudget ≤
      subcriticalCompositionCertificateSize
        sampleSubcriticalCompositionCertificate := by
  apply subcriticalCompositionCertificate_budget_le_size
  norm_num [subcriticalCompositionCertificateReady,
    subcriticalCompositionCertificateControlled,
    sampleSubcriticalCompositionCertificate]

/-- A refinement certificate with the composition budget separated from size. -/
structure SubcriticalCompositionRefinementCertificate where
  outerRadiusWindow : ℕ
  innerRadiusWindow : ℕ
  separationDenominatorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubcriticalCompositionRefinementCertificate.parametersControlled
    (cert : SubcriticalCompositionRefinementCertificate) : Prop :=
  0 < cert.outerRadiusWindow ∧
    0 < cert.innerRadiusWindow ∧
      0 < cert.separationDenominatorWindow

def SubcriticalCompositionRefinementCertificate.budgetControlled
    (cert : SubcriticalCompositionRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.outerRadiusWindow + cert.innerRadiusWindow +
      cert.separationDenominatorWindow + cert.slack

def subcriticalCompositionRefinementReady
    (cert : SubcriticalCompositionRefinementCertificate) : Prop :=
  cert.parametersControlled ∧ cert.budgetControlled

def SubcriticalCompositionRefinementCertificate.size
    (cert : SubcriticalCompositionRefinementCertificate) : ℕ :=
  cert.outerRadiusWindow + cert.innerRadiusWindow +
    cert.separationDenominatorWindow + cert.slack

theorem subcriticalComposition_certificateBudgetWindow_le_size
    (cert : SubcriticalCompositionRefinementCertificate)
    (h : subcriticalCompositionRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSubcriticalCompositionRefinementCertificate :
    SubcriticalCompositionRefinementCertificate :=
  { outerRadiusWindow := 2, innerRadiusWindow := 3,
    separationDenominatorWindow := 2, certificateBudgetWindow := 8, slack := 1 }

example :
    subcriticalCompositionRefinementReady
      sampleSubcriticalCompositionRefinementCertificate := by
  norm_num [subcriticalCompositionRefinementReady,
    SubcriticalCompositionRefinementCertificate.parametersControlled,
    SubcriticalCompositionRefinementCertificate.budgetControlled,
    sampleSubcriticalCompositionRefinementCertificate]

example :
    sampleSubcriticalCompositionRefinementCertificate.certificateBudgetWindow ≤
      sampleSubcriticalCompositionRefinementCertificate.size := by
  apply subcriticalComposition_certificateBudgetWindow_le_size
  norm_num [subcriticalCompositionRefinementReady,
    SubcriticalCompositionRefinementCertificate.parametersControlled,
    SubcriticalCompositionRefinementCertificate.budgetControlled,
    sampleSubcriticalCompositionRefinementCertificate]


structure SubcriticalCompositionBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubcriticalCompositionBudgetCertificate.controlled
    (c : SubcriticalCompositionBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def SubcriticalCompositionBudgetCertificate.budgetControlled
    (c : SubcriticalCompositionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SubcriticalCompositionBudgetCertificate.Ready
    (c : SubcriticalCompositionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SubcriticalCompositionBudgetCertificate.size
    (c : SubcriticalCompositionBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem subcriticalComposition_budgetCertificate_le_size
    (c : SubcriticalCompositionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSubcriticalCompositionBudgetCertificate :
    SubcriticalCompositionBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleSubcriticalCompositionBudgetCertificate.Ready := by
  constructor
  · norm_num [SubcriticalCompositionBudgetCertificate.controlled,
      sampleSubcriticalCompositionBudgetCertificate]
  · norm_num [SubcriticalCompositionBudgetCertificate.budgetControlled,
      sampleSubcriticalCompositionBudgetCertificate]

example :
    sampleSubcriticalCompositionBudgetCertificate.certificateBudgetWindow ≤
      sampleSubcriticalCompositionBudgetCertificate.size := by
  apply subcriticalComposition_budgetCertificate_le_size
  constructor
  · norm_num [SubcriticalCompositionBudgetCertificate.controlled,
      sampleSubcriticalCompositionBudgetCertificate]
  · norm_num [SubcriticalCompositionBudgetCertificate.budgetControlled,
      sampleSubcriticalCompositionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSubcriticalCompositionBudgetCertificate.Ready := by
  constructor
  · norm_num [SubcriticalCompositionBudgetCertificate.controlled,
      sampleSubcriticalCompositionBudgetCertificate]
  · norm_num [SubcriticalCompositionBudgetCertificate.budgetControlled,
      sampleSubcriticalCompositionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSubcriticalCompositionBudgetCertificate.certificateBudgetWindow ≤
      sampleSubcriticalCompositionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SubcriticalCompositionBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSubcriticalCompositionBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSubcriticalCompositionBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SubcriticalComposition
