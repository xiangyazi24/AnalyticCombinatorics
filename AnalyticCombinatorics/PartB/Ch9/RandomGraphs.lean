import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch9.RandomGraphs


/-- Total number of labelled graphs on n vertices: 2^(n choose 2). -/
def totalGraphs (n : ℕ) : ℕ := 2 ^ Nat.choose n 2

example : totalGraphs 0 = 1 := by native_decide
example : totalGraphs 1 = 1 := by native_decide
example : totalGraphs 2 = 2 := by native_decide
example : totalGraphs 3 = 8 := by native_decide
example : totalGraphs 4 = 64 := by native_decide
example : totalGraphs 5 = 1024 := by native_decide

/-- Number of connected labelled graphs on n vertices (OEIS A001187). -/
def connectedGraphTable : Fin 6 → ℕ
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 4 | ⟨4, _⟩ => 38 | ⟨5, _⟩ => 728

/-- Cayley's formula: the number of labelled trees on n vertices is n^(n-2). -/
def cayleyTreeCount (n : ℕ) : ℕ := if n ≤ 1 then 1 else n ^ (n - 2)

example : cayleyTreeCount 3 = 3 := by native_decide
example : cayleyTreeCount 4 = 16 := by native_decide
example : cayleyTreeCount 5 = 125 := by native_decide
example : cayleyTreeCount 6 = 1296 := by native_decide

/-- Trees ≤ Connected graphs ≤ Total graphs for n = 4, 5. -/
example : cayleyTreeCount 4 ≤ connectedGraphTable ⟨4, by omega⟩ := by native_decide
example : connectedGraphTable ⟨4, by omega⟩ ≤ totalGraphs 4 := by native_decide
example : cayleyTreeCount 5 ≤ connectedGraphTable ⟨5, by omega⟩ := by native_decide
example : connectedGraphTable ⟨5, by omega⟩ ≤ totalGraphs 5 := by native_decide

/-- Edge density at phase transition: number of possible edges = n choose 2. -/
example : Nat.choose 10 2 = 45 := by native_decide
example : Nat.choose 20 2 = 190 := by native_decide
example : Nat.choose 100 2 = 4950 := by native_decide

structure RandomGraphWindow where
  vertices : ℕ
  edges : ℕ
  possibleEdges : ℕ
  densitySlack : ℕ
deriving DecidableEq, Repr

def RandomGraphWindow.edgeSpaceReady (w : RandomGraphWindow) : Prop :=
  w.possibleEdges = Nat.choose w.vertices 2

def RandomGraphWindow.sparseControlled (w : RandomGraphWindow) : Prop :=
  w.edges ≤ w.vertices + w.densitySlack

def RandomGraphWindow.validSimpleGraph (w : RandomGraphWindow) : Prop :=
  w.edges ≤ w.possibleEdges

def RandomGraphWindow.certificate (w : RandomGraphWindow) : ℕ :=
  w.vertices + w.edges + w.possibleEdges + w.densitySlack

theorem edges_le_certificate (w : RandomGraphWindow) :
    w.edges ≤ w.certificate := by
  unfold RandomGraphWindow.certificate
  omega

def sampleRandomGraphWindow : RandomGraphWindow :=
  { vertices := 6, edges := 6, possibleEdges := 15, densitySlack := 0 }

example : sampleRandomGraphWindow.edgeSpaceReady := by
  unfold RandomGraphWindow.edgeSpaceReady
  native_decide

example : sampleRandomGraphWindow.sparseControlled := by
  norm_num [sampleRandomGraphWindow, RandomGraphWindow.sparseControlled]

example : sampleRandomGraphWindow.validSimpleGraph := by
  norm_num [sampleRandomGraphWindow, RandomGraphWindow.validSimpleGraph]


structure RandomGraphsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomGraphsBudgetCertificate.controlled
    (c : RandomGraphsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomGraphsBudgetCertificate.budgetControlled
    (c : RandomGraphsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomGraphsBudgetCertificate.Ready
    (c : RandomGraphsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomGraphsBudgetCertificate.size
    (c : RandomGraphsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomGraphs_budgetCertificate_le_size
    (c : RandomGraphsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomGraphsBudgetCertificate :
    RandomGraphsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomGraphsBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomGraphsBudgetCertificate.controlled,
      sampleRandomGraphsBudgetCertificate]
  · norm_num [RandomGraphsBudgetCertificate.budgetControlled,
      sampleRandomGraphsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomGraphsBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomGraphsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomGraphsBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomGraphsBudgetCertificate.controlled,
      sampleRandomGraphsBudgetCertificate]
  · norm_num [RandomGraphsBudgetCertificate.budgetControlled,
      sampleRandomGraphsBudgetCertificate]

example :
    sampleRandomGraphsBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomGraphsBudgetCertificate.size := by
  apply randomGraphs_budgetCertificate_le_size
  constructor
  · norm_num [RandomGraphsBudgetCertificate.controlled,
      sampleRandomGraphsBudgetCertificate]
  · norm_num [RandomGraphsBudgetCertificate.budgetControlled,
      sampleRandomGraphsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleRandomGraphsBudgetCertificate_ready :
    sampleRandomGraphsBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomGraphsBudgetCertificate.controlled,
      sampleRandomGraphsBudgetCertificate]
  · norm_num [RandomGraphsBudgetCertificate.budgetControlled,
      sampleRandomGraphsBudgetCertificate]

def budgetCertificateListReady (data : List RandomGraphsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomGraphsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRandomGraphsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.RandomGraphs
