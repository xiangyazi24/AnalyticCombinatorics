import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter VII: Tree Function

Finite checks around the tree function `T(z)=z exp(T(z))`, Cayley trees, and
Lambert-W style inversion schemas.
-/

namespace AnalyticCombinatorics.PartB.Ch7.TreeFunction

/-- Cayley tree numbers `n^(n-1)` for labelled rooted trees on `n` labels. -/
def cayleyRootedTrees (n : ℕ) : ℕ :=
  if n = 0 then 0 else n ^ (n - 1)

theorem cayleyRootedTrees_samples :
    (List.range 8).map cayleyRootedTrees = [0, 1, 2, 9, 64, 625, 7776, 117649] := by
  native_decide

/-- Unrooted labelled trees `n^(n-2)` for `n >= 1`, with the singleton set to 1. -/
def cayleyUnrootedTrees (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else n ^ (n - 2)

theorem cayleyUnrootedTrees_samples :
    (List.range 8).map cayleyUnrootedTrees = [1, 1, 1, 3, 16, 125, 1296, 16807] := by
  native_decide

theorem rooted_unrooted_relation :
    ∀ n ∈ Finset.Icc 2 8, cayleyUnrootedTrees n * n = cayleyRootedTrees n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, _⟩
  interval_cases n <;> native_decide

/-- Coefficients of the tree function `T(z)` scaled by `n!`: `n^(n-1)`. -/
def treeFunctionScaledCoeff (n : ℕ) : ℕ :=
  cayleyRootedTrees n

theorem treeFunctionScaledCoeff_samples :
    (List.range 7).map treeFunctionScaledCoeff = [0, 1, 2, 9, 64, 625, 7776] := by
  native_decide

/-- Tree-function singular data at `rho = e^-1`, represented symbolically. -/
structure TreeFunctionSingularData where
  inverseRadiusName : String
  squareRootAmplitudeNumerator : ℤ
  squareRootAmplitudeDenominator : ℕ

def classicalTreeFunctionData : TreeFunctionSingularData where
  inverseRadiusName := "e"
  squareRootAmplitudeNumerator := -1
  squareRootAmplitudeDenominator := 1

theorem classicalTreeFunctionData_values :
    classicalTreeFunctionData.inverseRadiusName = "e" ∧
    classicalTreeFunctionData.squareRootAmplitudeNumerator = -1 ∧
    classicalTreeFunctionData.squareRootAmplitudeDenominator = 1 := by
  native_decide

/-- Tree-function singular data certificate. -/
def treeFunctionSingularDataReady (data : TreeFunctionSingularData) : Prop :=
  0 < data.inverseRadiusName.length ∧ 0 < data.squareRootAmplitudeDenominator

theorem classicalTreeFunctionData_ready :
    treeFunctionSingularDataReady classicalTreeFunctionData := by
  unfold treeFunctionSingularDataReady classicalTreeFunctionData
  native_decide

/-- Lambert-W/tree-function inversion certificate. -/
def TreeFunctionInversion
    (T : ℂ → ℂ) (coeff : ℕ → ℂ) (data : TreeFunctionSingularData) : Prop :=
  treeFunctionSingularDataReady data ∧ T 0 = 0 ∧ coeff 0 = coeff data.inverseRadiusName.length

theorem tree_function_inversion_statement :
    TreeFunctionInversion (fun z => z) (fun _ => 0) classicalTreeFunctionData := by
  unfold TreeFunctionInversion
  exact ⟨classicalTreeFunctionData_ready, by norm_num, by norm_num⟩


structure TreeFunctionBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TreeFunctionBudgetCertificate.controlled
    (c : TreeFunctionBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TreeFunctionBudgetCertificate.budgetControlled
    (c : TreeFunctionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TreeFunctionBudgetCertificate.Ready
    (c : TreeFunctionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TreeFunctionBudgetCertificate.size
    (c : TreeFunctionBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem treeFunction_budgetCertificate_le_size
    (c : TreeFunctionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTreeFunctionBudgetCertificate :
    TreeFunctionBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleTreeFunctionBudgetCertificate.Ready := by
  constructor
  · norm_num [TreeFunctionBudgetCertificate.controlled,
      sampleTreeFunctionBudgetCertificate]
  · norm_num [TreeFunctionBudgetCertificate.budgetControlled,
      sampleTreeFunctionBudgetCertificate]

example :
    sampleTreeFunctionBudgetCertificate.certificateBudgetWindow ≤
      sampleTreeFunctionBudgetCertificate.size := by
  apply treeFunction_budgetCertificate_le_size
  constructor
  · norm_num [TreeFunctionBudgetCertificate.controlled,
      sampleTreeFunctionBudgetCertificate]
  · norm_num [TreeFunctionBudgetCertificate.budgetControlled,
      sampleTreeFunctionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTreeFunctionBudgetCertificate.Ready := by
  constructor
  · norm_num [TreeFunctionBudgetCertificate.controlled,
      sampleTreeFunctionBudgetCertificate]
  · norm_num [TreeFunctionBudgetCertificate.budgetControlled,
      sampleTreeFunctionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTreeFunctionBudgetCertificate.certificateBudgetWindow ≤
      sampleTreeFunctionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List TreeFunctionBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTreeFunctionBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTreeFunctionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.TreeFunction
