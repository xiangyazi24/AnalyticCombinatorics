import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite matching models.

Edges are list-encoded pairs.  The definitions track matching sizes and
endpoint budgets for small graph specifications.
-/

namespace AnalyticCombinatorics.AppA.FiniteMatchingModels

def endpointMass (edges : List (ℕ × ℕ)) : ℕ :=
  edges.map (fun e => e.1 + e.2) |>.sum

def matchingSize (edges : List (ℕ × ℕ)) : ℕ :=
  edges.length

def edgeWeight (e : ℕ × ℕ) : ℕ :=
  e.1 + e.2

def boundedEdgeWeight (edges : List (ℕ × ℕ)) (bound : ℕ) : Prop :=
  ∀ e ∈ edges, edgeWeight e ≤ bound

theorem matchingSize_nil :
    matchingSize [] = 0 := by
  rfl

theorem matchingSize_cons (e : ℕ × ℕ) (edges : List (ℕ × ℕ)) :
    matchingSize (e :: edges) = matchingSize edges + 1 := by
  simp [matchingSize]

theorem boundedEdgeWeight_mono {edges : List (ℕ × ℕ)} {b c : ℕ}
    (h : boundedEdgeWeight edges b) (hbc : b ≤ c) :
    boundedEdgeWeight edges c := by
  intro e he
  exact le_trans (h e he) hbc

def sampleMatching : List (ℕ × ℕ) :=
  [(0, 2), (1, 3), (4, 5)]

example : matchingSize sampleMatching = 3 := by
  native_decide

example : endpointMass sampleMatching = 15 := by
  native_decide

example : boundedEdgeWeight sampleMatching 9 := by
  intro e he
  simp only [sampleMatching, List.mem_cons, List.not_mem_nil] at he
  rcases he with rfl | he
  · native_decide
  rcases he with rfl | he
  · native_decide
  rcases he with rfl | he
  · native_decide
  · cases he


structure FiniteMatchingModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteMatchingModelsBudgetCertificate.controlled
    (c : FiniteMatchingModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteMatchingModelsBudgetCertificate.budgetControlled
    (c : FiniteMatchingModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteMatchingModelsBudgetCertificate.Ready
    (c : FiniteMatchingModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteMatchingModelsBudgetCertificate.size
    (c : FiniteMatchingModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteMatchingModels_budgetCertificate_le_size
    (c : FiniteMatchingModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteMatchingModelsBudgetCertificate :
    FiniteMatchingModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteMatchingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteMatchingModelsBudgetCertificate.controlled,
      sampleFiniteMatchingModelsBudgetCertificate]
  · norm_num [FiniteMatchingModelsBudgetCertificate.budgetControlled,
      sampleFiniteMatchingModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteMatchingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteMatchingModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteMatchingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteMatchingModelsBudgetCertificate.controlled,
      sampleFiniteMatchingModelsBudgetCertificate]
  · norm_num [FiniteMatchingModelsBudgetCertificate.budgetControlled,
      sampleFiniteMatchingModelsBudgetCertificate]

example :
    sampleFiniteMatchingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteMatchingModelsBudgetCertificate.size := by
  apply finiteMatchingModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteMatchingModelsBudgetCertificate.controlled,
      sampleFiniteMatchingModelsBudgetCertificate]
  · norm_num [FiniteMatchingModelsBudgetCertificate.budgetControlled,
      sampleFiniteMatchingModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteMatchingModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteMatchingModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteMatchingModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteMatchingModels
