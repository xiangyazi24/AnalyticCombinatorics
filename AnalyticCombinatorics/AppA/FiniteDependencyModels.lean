import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite dependency models.

Dependencies are list-encoded directed edges.  The module records edge
counts and local dependency loads.
-/

namespace AnalyticCombinatorics.AppA.FiniteDependencyModels

def dependsOn (edges : List (ℕ × ℕ)) (a b : ℕ) : Bool :=
  edges.any (fun e => e.1 == a && e.2 == b)

def dependencyCount (edges : List (ℕ × ℕ)) : ℕ :=
  edges.length

def outgoingDependencyCount (edges : List (ℕ × ℕ)) (a : ℕ) : ℕ :=
  edges.filter (fun e => e.1 == a) |>.length

def dependencyBudgeted (edges : List (ℕ × ℕ)) (budget : ℕ) : Prop :=
  dependencyCount edges ≤ budget

theorem dependencyCount_nil :
    dependencyCount [] = 0 := by
  rfl

theorem dependencyCount_cons (e : ℕ × ℕ) (edges : List (ℕ × ℕ)) :
    dependencyCount (e :: edges) = dependencyCount edges + 1 := by
  simp [dependencyCount]

def sampleDependencies : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (2, 3), (3, 1)]

example : dependsOn sampleDependencies 0 2 = true := by
  native_decide

example : outgoingDependencyCount sampleDependencies 0 = 2 := by
  native_decide

example : dependencyBudgeted sampleDependencies 5 := by
  norm_num [dependencyBudgeted, dependencyCount, sampleDependencies]

structure DependencyWindow where
  nodes : ℕ
  edges : ℕ
  maxOutDegree : ℕ
  longestChain : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DependencyWindow.edgeControlled (w : DependencyWindow) : Prop :=
  w.edges ≤ w.nodes * w.maxOutDegree + w.slack

def DependencyWindow.chainControlled (w : DependencyWindow) : Prop :=
  w.longestChain ≤ w.nodes + w.slack

def DependencyWindow.ready (w : DependencyWindow) : Prop :=
  w.edgeControlled ∧ w.chainControlled

def DependencyWindow.certificate (w : DependencyWindow) : ℕ :=
  w.nodes + w.edges + w.maxOutDegree + w.longestChain + w.slack

theorem longestChain_le_certificate (w : DependencyWindow) :
    w.longestChain ≤ w.certificate := by
  unfold DependencyWindow.certificate
  omega

def sampleDependencyWindow : DependencyWindow :=
  { nodes := 4, edges := 4, maxOutDegree := 2, longestChain := 3, slack := 0 }

example : sampleDependencyWindow.ready := by
  norm_num [sampleDependencyWindow, DependencyWindow.ready,
    DependencyWindow.edgeControlled, DependencyWindow.chainControlled]


structure FiniteDependencyModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteDependencyModelsBudgetCertificate.controlled
    (c : FiniteDependencyModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteDependencyModelsBudgetCertificate.budgetControlled
    (c : FiniteDependencyModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteDependencyModelsBudgetCertificate.Ready
    (c : FiniteDependencyModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteDependencyModelsBudgetCertificate.size
    (c : FiniteDependencyModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteDependencyModels_budgetCertificate_le_size
    (c : FiniteDependencyModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteDependencyModelsBudgetCertificate :
    FiniteDependencyModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteDependencyModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteDependencyModelsBudgetCertificate.controlled,
      sampleFiniteDependencyModelsBudgetCertificate]
  · norm_num [FiniteDependencyModelsBudgetCertificate.budgetControlled,
      sampleFiniteDependencyModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteDependencyModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteDependencyModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteDependencyModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteDependencyModelsBudgetCertificate.controlled,
      sampleFiniteDependencyModelsBudgetCertificate]
  · norm_num [FiniteDependencyModelsBudgetCertificate.budgetControlled,
      sampleFiniteDependencyModelsBudgetCertificate]

example :
    sampleFiniteDependencyModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteDependencyModelsBudgetCertificate.size := by
  apply finiteDependencyModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteDependencyModelsBudgetCertificate.controlled,
      sampleFiniteDependencyModelsBudgetCertificate]
  · norm_num [FiniteDependencyModelsBudgetCertificate.budgetControlled,
      sampleFiniteDependencyModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteDependencyModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteDependencyModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteDependencyModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteDependencyModels
