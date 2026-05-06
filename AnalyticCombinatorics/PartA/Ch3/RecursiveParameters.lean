import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Recursive parameters.

Finite dependency-window bookkeeping for parameters defined by recursive
combinatorial specifications.
-/

namespace AnalyticCombinatorics.PartA.Ch3.RecursiveParameters

/-- Recursive additive parameter model on tree-like structures. -/
def recursiveParameter : ℕ → ℕ
  | 0 => 0
  | n + 1 => recursiveParameter n + 1

/-- Finite audit that the recursively defined parameter stays size-bounded. -/
def recursiveParameterBoundCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => recursiveParameter n ≤ n

/-- Finite dependency-depth check for a unary recursive specification. -/
def dependencyDepthCheck (depth N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => recursiveParameter n ≤ n * depth

theorem recursiveParameter_identity_window :
    recursiveParameterBoundCheck 32 = true := by
  unfold recursiveParameterBoundCheck recursiveParameter
  native_decide

theorem recursiveParameter_dependency_window :
    dependencyDepthCheck 1 32 = true := by
  unfold dependencyDepthCheck recursiveParameter
  native_decide

/-- Prefix sum of the recursive parameter samples. -/
def recursiveParameterPrefix (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + recursiveParameter n) 0

theorem recursiveParameterPrefix_window :
    recursiveParameterPrefix 6 = 21 := by
  unfold recursiveParameterPrefix recursiveParameter
  native_decide

structure RecursiveParameterWindow where
  equationCount : ℕ
  dependencyDepth : ℕ
  parameterDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def recursiveParameterReady (w : RecursiveParameterWindow) : Prop :=
  0 < w.equationCount ∧
    w.parameterDepth ≤ w.equationCount + w.dependencyDepth + w.slack

def recursiveParameterBudget (w : RecursiveParameterWindow) : ℕ :=
  w.equationCount + w.dependencyDepth + w.parameterDepth + w.slack

theorem parameterDepth_le_recursiveBudget
    (w : RecursiveParameterWindow) :
    w.parameterDepth ≤ recursiveParameterBudget w := by
  unfold recursiveParameterBudget
  omega

def sampleRecursiveParameterWindow : RecursiveParameterWindow :=
  { equationCount := 4, dependencyDepth := 5, parameterDepth := 8, slack := 1 }

example : recursiveParameterReady sampleRecursiveParameterWindow := by
  norm_num [recursiveParameterReady, sampleRecursiveParameterWindow]

structure RecursiveParametersBudgetCertificate where
  equationWindow : ℕ
  dependencyWindow : ℕ
  parameterWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RecursiveParametersBudgetCertificate.controlled
    (c : RecursiveParametersBudgetCertificate) : Prop :=
  0 < c.equationWindow ∧
    c.parameterWindow ≤ c.equationWindow + c.dependencyWindow + c.slack

def RecursiveParametersBudgetCertificate.budgetControlled
    (c : RecursiveParametersBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.equationWindow + c.dependencyWindow + c.parameterWindow + c.slack

def RecursiveParametersBudgetCertificate.Ready
    (c : RecursiveParametersBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RecursiveParametersBudgetCertificate.size
    (c : RecursiveParametersBudgetCertificate) : ℕ :=
  c.equationWindow + c.dependencyWindow + c.parameterWindow + c.slack

theorem recursiveParameters_budgetCertificate_le_size
    (c : RecursiveParametersBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleRecursiveParametersBudgetCertificate :
    RecursiveParametersBudgetCertificate :=
  { equationWindow := 4
    dependencyWindow := 5
    parameterWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

example : sampleRecursiveParametersBudgetCertificate.Ready := by
  constructor
  · norm_num [RecursiveParametersBudgetCertificate.controlled,
      sampleRecursiveParametersBudgetCertificate]
  · norm_num [RecursiveParametersBudgetCertificate.budgetControlled,
      sampleRecursiveParametersBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRecursiveParametersBudgetCertificate.Ready := by
  constructor
  · norm_num [RecursiveParametersBudgetCertificate.controlled,
      sampleRecursiveParametersBudgetCertificate]
  · norm_num [RecursiveParametersBudgetCertificate.budgetControlled,
      sampleRecursiveParametersBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRecursiveParametersBudgetCertificate.certificateBudgetWindow ≤
      sampleRecursiveParametersBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RecursiveParametersBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleRecursiveParametersBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleRecursiveParametersBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.RecursiveParameters
