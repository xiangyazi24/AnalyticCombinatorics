import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace GraphTheory

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

end GraphTheory
