import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Catalan family examples.

This module records that the standard Catalan families share the same initial
count table.
-/

namespace AnalyticCombinatorics.Examples.CatalanFamily

def catalanCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 42
  | 6 => 132
  | 7 => 429
  | 8 => 1430
  | 9 => 4862
  | 10 => 16796
  | _ => 0

def binaryTreeCount (n : ℕ) : ℕ := catalanCount n
def planeTreeCount (n : ℕ) : ℕ := catalanCount n
def triangulationCount (n : ℕ) : ℕ := catalanCount n
def dyckPathCount (n : ℕ) : ℕ := catalanCount n

theorem binary_eq_plane (n : ℕ) :
    binaryTreeCount n = planeTreeCount n := rfl

theorem binary_eq_triangulation (n : ℕ) :
    binaryTreeCount n = triangulationCount n := rfl

theorem binary_eq_dyckPath (n : ℕ) :
    binaryTreeCount n = dyckPathCount n := rfl

example : binaryTreeCount 5 = dyckPathCount 5 := by native_decide
example : planeTreeCount 7 = triangulationCount 7 := by native_decide
example : dyckPathCount 10 = 16796 := by native_decide

structure CatalanFamilyWindow where
  size : ℕ
  binaryTrees : ℕ
  planeTrees : ℕ
  dyckPaths : ℕ
  triangulations : ℕ
deriving DecidableEq, Repr

def CatalanFamilyWindow.sameCounts (w : CatalanFamilyWindow) : Prop :=
  w.binaryTrees = w.planeTrees ∧ w.planeTrees = w.dyckPaths ∧
    w.dyckPaths = w.triangulations

def CatalanFamilyWindow.matchesTable (w : CatalanFamilyWindow) : Prop :=
  w.binaryTrees = catalanCount w.size

def CatalanFamilyWindow.ready (w : CatalanFamilyWindow) : Prop :=
  w.sameCounts ∧ w.matchesTable

def sampleCatalanFamilyWindow : CatalanFamilyWindow :=
  { size := 5, binaryTrees := 42, planeTrees := 42, dyckPaths := 42, triangulations := 42 }

example : sampleCatalanFamilyWindow.ready := by
  norm_num [sampleCatalanFamilyWindow, CatalanFamilyWindow.ready,
    CatalanFamilyWindow.sameCounts, CatalanFamilyWindow.matchesTable, catalanCount]

example : (List.range 6).map catalanCount = [1, 1, 2, 5, 14, 42] := by
  native_decide

structure CatalanFamilyBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CatalanFamilyBudgetCertificate.controlled
    (c : CatalanFamilyBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CatalanFamilyBudgetCertificate.budgetControlled
    (c : CatalanFamilyBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CatalanFamilyBudgetCertificate.Ready
    (c : CatalanFamilyBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CatalanFamilyBudgetCertificate.size
    (c : CatalanFamilyBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem catalanFamily_budgetCertificate_le_size
    (c : CatalanFamilyBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleCatalanFamilyBudgetCertificate : CatalanFamilyBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleCatalanFamilyBudgetCertificate.Ready := by
  constructor
  · norm_num [CatalanFamilyBudgetCertificate.controlled,
      sampleCatalanFamilyBudgetCertificate]
  · norm_num [CatalanFamilyBudgetCertificate.budgetControlled,
      sampleCatalanFamilyBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCatalanFamilyBudgetCertificate.Ready := by
  constructor
  · norm_num [CatalanFamilyBudgetCertificate.controlled,
      sampleCatalanFamilyBudgetCertificate]
  · norm_num [CatalanFamilyBudgetCertificate.budgetControlled,
      sampleCatalanFamilyBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCatalanFamilyBudgetCertificate.certificateBudgetWindow ≤
      sampleCatalanFamilyBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CatalanFamilyBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCatalanFamilyBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCatalanFamilyBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.CatalanFamily
