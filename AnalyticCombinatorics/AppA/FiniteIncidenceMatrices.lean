import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite incidence-matrix helpers.

Incidence matrices are represented by row lists with natural entries, useful
for finite species and graph-counting examples.
-/

namespace AnalyticCombinatorics.AppA.FiniteIncidenceMatrices

def rowSum (row : List ℕ) : ℕ :=
  row.sum

def matrixMass (rows : List (List ℕ)) : ℕ :=
  rows.map rowSum |>.sum

def rowCount (rows : List (List ℕ)) : ℕ :=
  rows.length

def rectangularWithWidth (rows : List (List ℕ)) (width : ℕ) : Prop :=
  ∀ row ∈ rows, row.length = width

theorem matrixMass_nil :
    matrixMass [] = 0 := by
  rfl

theorem rowCount_cons (row : List ℕ) (rows : List (List ℕ)) :
    rowCount (row :: rows) = rowCount rows + 1 := by
  simp [rowCount]

theorem rectangularWithWidth_tail {row : List ℕ} {rows : List (List ℕ)} {width : ℕ}
    (h : rectangularWithWidth (row :: rows) width) :
    rectangularWithWidth rows width := by
  intro r hr
  exact h r (by simp [hr])

def sampleMatrix : List (List ℕ) :=
  [[1, 0, 1], [0, 1, 1], [1, 1, 0]]

example : rowSum [1, 0, 1] = 2 := by
  native_decide

example : matrixMass sampleMatrix = 6 := by
  native_decide

example : rectangularWithWidth sampleMatrix 3 := by
  intro row hrow
  simp only [sampleMatrix, List.mem_cons, List.not_mem_nil] at hrow
  rcases hrow with rfl | hrow
  · rfl
  rcases hrow with rfl | hrow
  · rfl
  rcases hrow with rfl | hrow
  · rfl
  · cases hrow


structure FiniteIncidenceMatricesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteIncidenceMatricesBudgetCertificate.controlled
    (c : FiniteIncidenceMatricesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteIncidenceMatricesBudgetCertificate.budgetControlled
    (c : FiniteIncidenceMatricesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteIncidenceMatricesBudgetCertificate.Ready
    (c : FiniteIncidenceMatricesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteIncidenceMatricesBudgetCertificate.size
    (c : FiniteIncidenceMatricesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteIncidenceMatrices_budgetCertificate_le_size
    (c : FiniteIncidenceMatricesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteIncidenceMatricesBudgetCertificate :
    FiniteIncidenceMatricesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteIncidenceMatricesBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteIncidenceMatricesBudgetCertificate.controlled,
      sampleFiniteIncidenceMatricesBudgetCertificate]
  · norm_num [FiniteIncidenceMatricesBudgetCertificate.budgetControlled,
      sampleFiniteIncidenceMatricesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteIncidenceMatricesBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteIncidenceMatricesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteIncidenceMatricesBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteIncidenceMatricesBudgetCertificate.controlled,
      sampleFiniteIncidenceMatricesBudgetCertificate]
  · norm_num [FiniteIncidenceMatricesBudgetCertificate.budgetControlled,
      sampleFiniteIncidenceMatricesBudgetCertificate]

example :
    sampleFiniteIncidenceMatricesBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteIncidenceMatricesBudgetCertificate.size := by
  apply finiteIncidenceMatrices_budgetCertificate_le_size
  constructor
  · norm_num [FiniteIncidenceMatricesBudgetCertificate.controlled,
      sampleFiniteIncidenceMatricesBudgetCertificate]
  · norm_num [FiniteIncidenceMatricesBudgetCertificate.budgetControlled,
      sampleFiniteIncidenceMatricesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteIncidenceMatricesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteIncidenceMatricesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteIncidenceMatricesBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteIncidenceMatrices
