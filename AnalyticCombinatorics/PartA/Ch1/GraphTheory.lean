import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.GraphTheory


def completeGraphEdges : Fin 9 → ℕ := ![1, 3, 6, 10, 15, 21, 28, 36, 45]

theorem completeGraphEdges_eq_choose :
    ∀ i : Fin 9, completeGraphEdges i = (i.1 + 2).choose 2 := by
  native_decide

def completeGraphHandshakeValues : Fin 6 → ℕ := ![3, 4, 5, 6, 7, 8]

theorem completeGraph_handshaking :
    ∀ i : Fin 6,
      2 * ((completeGraphHandshakeValues i).choose 2)
        = (completeGraphHandshakeValues i) * ((completeGraphHandshakeValues i) - 1) := by
  native_decide

def platonicVertices : Fin 5 → ℕ := ![4, 8, 6, 20, 12]

def platonicEdges : Fin 5 → ℕ := ![6, 12, 12, 30, 30]

def platonicFaces : Fin 5 → ℕ := ![4, 6, 8, 12, 20]

theorem platonicEulerFormula :
    ∀ i : Fin 5, (platonicVertices i : ℤ) - (platonicEdges i : ℤ) + (platonicFaces i : ℤ) = 2 := by
  native_decide

def treeVertices : Fin 7 → ℕ := ![1, 2, 3, 4, 5, 6, 7]

def treeEdges : Fin 7 → ℕ := ![0, 1, 2, 3, 4, 5, 6]

theorem treeEdges_eq_vertices_sub_one :
    ∀ i : Fin 7, treeEdges i = treeVertices i - 1 := by
  native_decide

def cayleyLabelledTrees : Fin 7 → ℕ := ![1, 1, 3, 16, 125, 1296, 16807]

theorem cayleyLabelledTrees_eq_power :
    ∀ i : Fin 7, cayleyLabelledTrees i = (treeVertices i) ^ ((treeVertices i) - 2) := by
  native_decide

def chromaticK3Values : Fin 3 → ℕ := ![6, 24, 60]

theorem chromaticK3_fallingFactorial :
    ∀ i : Fin 3,
      chromaticK3Values i = (i.1 + 3) * ((i.1 + 3) - 1) * ((i.1 + 3) - 2) := by
  native_decide

theorem ramsey33_completeGraphEdges : ((6 : ℕ).choose 2) = 15 := by
  native_decide

theorem ramsey33_twoColorings : 2 ^ (15 : ℕ) = 32768 := by
  native_decide



structure GraphTheoryBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GraphTheoryBudgetCertificate.controlled
    (c : GraphTheoryBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def GraphTheoryBudgetCertificate.budgetControlled
    (c : GraphTheoryBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def GraphTheoryBudgetCertificate.Ready
    (c : GraphTheoryBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GraphTheoryBudgetCertificate.size
    (c : GraphTheoryBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem graphTheory_budgetCertificate_le_size
    (c : GraphTheoryBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGraphTheoryBudgetCertificate :
    GraphTheoryBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleGraphTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [GraphTheoryBudgetCertificate.controlled,
      sampleGraphTheoryBudgetCertificate]
  · norm_num [GraphTheoryBudgetCertificate.budgetControlled,
      sampleGraphTheoryBudgetCertificate]

example :
    sampleGraphTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleGraphTheoryBudgetCertificate.size := by
  apply graphTheory_budgetCertificate_le_size
  constructor
  · norm_num [GraphTheoryBudgetCertificate.controlled,
      sampleGraphTheoryBudgetCertificate]
  · norm_num [GraphTheoryBudgetCertificate.budgetControlled,
      sampleGraphTheoryBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleGraphTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [GraphTheoryBudgetCertificate.controlled,
      sampleGraphTheoryBudgetCertificate]
  · norm_num [GraphTheoryBudgetCertificate.budgetControlled,
      sampleGraphTheoryBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGraphTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleGraphTheoryBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List GraphTheoryBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGraphTheoryBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleGraphTheoryBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.GraphTheory
