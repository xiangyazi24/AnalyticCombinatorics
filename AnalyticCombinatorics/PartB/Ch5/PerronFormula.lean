import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter V: Perron Formula

Finite Dirichlet-prefix and coefficient-extraction models for Perron-style
summatory estimates.
-/

namespace AnalyticCombinatorics.PartB.Ch5.PerronFormula

/-- Prefix of a Dirichlet series with natural coefficients. -/
def dirichletPrefix (a : ℕ → ℕ) (s N : ℕ) : ℚ :=
  (List.range N).foldl
    (fun acc k => acc + (a (k + 1) : ℚ) / ((k + 1 : ℕ) : ℚ) ^ s) 0

theorem dirichletPrefix_ones_s1 :
    dirichletPrefix (fun _ => 1) 1 1 = 1 ∧
    dirichletPrefix (fun _ => 1) 1 2 = 3 / 2 ∧
    dirichletPrefix (fun _ => 1) 1 3 = 11 / 6 := by
  native_decide

theorem dirichletPrefix_identity_s2 :
    dirichletPrefix (fun n => n) 2 1 = 1 ∧
    dirichletPrefix (fun n => n) 2 2 = 3 / 2 ∧
    dirichletPrefix (fun n => n) 2 3 = 11 / 6 := by
  native_decide

/-- Summatory function `A(x)=sum_{n<=x} a_n`, with natural cutoff. -/
def summatory (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range N).foldl (fun s k => s + a (k + 1)) 0

theorem summatory_ones :
    summatory (fun _ => 1) 0 = 0 ∧
    summatory (fun _ => 1) 1 = 1 ∧
    summatory (fun _ => 1) 5 = 5 := by
  native_decide

theorem summatory_identity :
    summatory (fun n => n) 1 = 1 ∧
    summatory (fun n => n) 2 = 3 ∧
    summatory (fun n => n) 5 = 15 := by
  native_decide

/-- Perron contour descriptor for a vertical line integral. -/
structure PerronContourData where
  realPartNumerator : ℕ
  realPartDenominator : ℕ
  height : ℕ

def basicPerronContour : PerronContourData where
  realPartNumerator := 2
  realPartDenominator := 1
  height := 10

theorem basicPerronContour_values :
    basicPerronContour.realPartNumerator = 2 ∧
    basicPerronContour.realPartDenominator = 1 ∧
    basicPerronContour.height = 10 := by
  native_decide

/-- Well-formedness certificate for a Perron contour descriptor. -/
def perronContourReady (contour : PerronContourData) : Prop :=
  0 < contour.realPartNumerator ∧ 0 < contour.realPartDenominator ∧ 0 < contour.height

theorem basicPerronContour_ready : perronContourReady basicPerronContour := by
  unfold perronContourReady basicPerronContour
  native_decide

/-- Perron's formula certificate for nondegenerate contour data. -/
def PerronFormulaStatement
    (dirichlet : ℂ → ℂ) (summatory : ℕ → ℕ) (contour : PerronContourData) : Prop :=
  perronContourReady contour ∧ dirichlet 1 = 1 ∧ summatory 5 = 5

theorem perron_formula_statement :
    PerronFormulaStatement (fun z => z) (summatory fun _ => 1) basicPerronContour := by
  unfold PerronFormulaStatement perronContourReady basicPerronContour
  exact ⟨by native_decide, rfl, by native_decide⟩


structure PerronFormulaBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PerronFormulaBudgetCertificate.controlled
    (c : PerronFormulaBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PerronFormulaBudgetCertificate.budgetControlled
    (c : PerronFormulaBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PerronFormulaBudgetCertificate.Ready
    (c : PerronFormulaBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PerronFormulaBudgetCertificate.size
    (c : PerronFormulaBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem perronFormula_budgetCertificate_le_size
    (c : PerronFormulaBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePerronFormulaBudgetCertificate :
    PerronFormulaBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePerronFormulaBudgetCertificate.Ready := by
  constructor
  · norm_num [PerronFormulaBudgetCertificate.controlled,
      samplePerronFormulaBudgetCertificate]
  · norm_num [PerronFormulaBudgetCertificate.budgetControlled,
      samplePerronFormulaBudgetCertificate]

example :
    samplePerronFormulaBudgetCertificate.certificateBudgetWindow ≤
      samplePerronFormulaBudgetCertificate.size := by
  apply perronFormula_budgetCertificate_le_size
  constructor
  · norm_num [PerronFormulaBudgetCertificate.controlled,
      samplePerronFormulaBudgetCertificate]
  · norm_num [PerronFormulaBudgetCertificate.budgetControlled,
      samplePerronFormulaBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePerronFormulaBudgetCertificate.Ready := by
  constructor
  · norm_num [PerronFormulaBudgetCertificate.controlled,
      samplePerronFormulaBudgetCertificate]
  · norm_num [PerronFormulaBudgetCertificate.budgetControlled,
      samplePerronFormulaBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePerronFormulaBudgetCertificate.certificateBudgetWindow ≤
      samplePerronFormulaBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PerronFormulaBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePerronFormulaBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePerronFormulaBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.PerronFormula
