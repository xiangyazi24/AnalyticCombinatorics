import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch7.ContextFreeSchemes


/-!
Chapter VII context-free and implicit-function schemes, in a finite
computational form.  The analytic statements are represented by records
describing the specification and its square-root transfer type; all theorems
below are exact coefficient checks that Lean can close by `native_decide`.
-/

/-! ## Context-free polynomial schemes -/

/-- A monomial `z^atoms * product variables`. -/
structure Term where
  atoms : Nat
  varIds : List Nat
deriving Repr, DecidableEq

/-- One equation of a polynomial context-free system. -/
structure Equation where
  lhs : Nat
  rhs : List Term
deriving Repr, DecidableEq

/-- A finite system of polynomial equations for ordinary generating functions. -/
structure SpecificationScheme where
  variableCount : Nat
  equations : List Equation
deriving Repr, DecidableEq

/-- The square-root singular shape used by smooth implicit-function schemes.
The growth constant is stored as a rational interval, so irrational constants
can be represented without pretending they are rational. -/
structure SquareRootAnalysis where
  scheme : SpecificationScheme
  rhoLowerNumerator : Nat
  rhoLowerDenominator : Nat
  rhoUpperNumerator : Nat
  rhoUpperDenominator : Nat
  growthLowerNumerator : Nat
  growthLowerDenominator : Nat
  growthUpperNumerator : Nat
  growthUpperDenominator : Nat
  transferExponentNumerator : Nat
  transferExponentDenominator : Nat
  checkedCoefficients : List Nat
deriving Repr, DecidableEq

def epsilonTerm : Term := { atoms := 0, varIds := [] }

def atomTerm : Term := { atoms := 1, varIds := [] }

def zTimes (vars : List Nat) : Term := { atoms := 1, varIds := vars }

/-! ## 1. Dyck paths -/

/-- Catalan number `C_n = binom(2n,n)/(n+1)`. -/
def catalan (n : Nat) : Nat := Nat.choose (2 * n) n / (n + 1)

/-- Dyck paths of semilength `n`. -/
def dyckPathCount (n : Nat) : Nat := catalan n

/-- The specification `D = 1 + z D^2`. -/
def dyckScheme : SpecificationScheme :=
  { variableCount := 1
    equations := [{ lhs := 0, rhs := [epsilonTerm, zTimes [0, 0]] }] }

def catalanSquareRootAnalysis : SquareRootAnalysis :=
  { scheme := dyckScheme
    rhoLowerNumerator := 1
    rhoLowerDenominator := 4
    rhoUpperNumerator := 1
    rhoUpperDenominator := 4
    growthLowerNumerator := 4
    growthLowerDenominator := 1
    growthUpperNumerator := 4
    growthUpperDenominator := 1
    transferExponentNumerator := 3
    transferExponentDenominator := 2
    checkedCoefficients := [1, 1, 2, 5, 14, 42, 132, 429, 1430] }

theorem dyck_catalan_values :
    [dyckPathCount 0, dyckPathCount 1, dyckPathCount 2, dyckPathCount 3,
     dyckPathCount 4, dyckPathCount 5, dyckPathCount 6, dyckPathCount 7,
     dyckPathCount 8] =
    [1, 1, 2, 5, 14, 42, 132, 429, 1430] := by native_decide

theorem dyck_catalan_formula_0_to_8 :
    [dyckPathCount 0, dyckPathCount 1, dyckPathCount 2, dyckPathCount 3,
     dyckPathCount 4, dyckPathCount 5, dyckPathCount 6, dyckPathCount 7,
     dyckPathCount 8] =
    [Nat.choose (2 * 0) 0 / (0 + 1), Nat.choose (2 * 1) 1 / (1 + 1),
     Nat.choose (2 * 2) 2 / (2 + 1), Nat.choose (2 * 3) 3 / (3 + 1),
     Nat.choose (2 * 4) 4 / (4 + 1), Nat.choose (2 * 5) 5 / (5 + 1),
     Nat.choose (2 * 6) 6 / (6 + 1), Nat.choose (2 * 7) 7 / (7 + 1),
     Nat.choose (2 * 8) 8 / (8 + 1)] := by native_decide

theorem dyck_convolution_0_to_6 :
    dyckPathCount 1 =
      (∑ k ∈ Finset.range 1, dyckPathCount k * dyckPathCount (0 - k)) ∧
    dyckPathCount 2 =
      (∑ k ∈ Finset.range 2, dyckPathCount k * dyckPathCount (1 - k)) ∧
    dyckPathCount 3 =
      (∑ k ∈ Finset.range 3, dyckPathCount k * dyckPathCount (2 - k)) ∧
    dyckPathCount 4 =
      (∑ k ∈ Finset.range 4, dyckPathCount k * dyckPathCount (3 - k)) ∧
    dyckPathCount 5 =
      (∑ k ∈ Finset.range 5, dyckPathCount k * dyckPathCount (4 - k)) ∧
    dyckPathCount 6 =
      (∑ k ∈ Finset.range 6, dyckPathCount k * dyckPathCount (5 - k)) ∧
    dyckPathCount 7 =
      (∑ k ∈ Finset.range 7, dyckPathCount k * dyckPathCount (6 - k)) := by
  native_decide

/-! ## 2. Balanced parentheses -/

/-- Balanced parenthesis words with `n` pairs; same specification as Dyck paths. -/
def balancedParenthesesCount (n : Nat) : Nat := dyckPathCount n

def balancedParenthesesScheme : SpecificationScheme := dyckScheme

theorem balanced_parentheses_values :
    [balancedParenthesesCount 0, balancedParenthesesCount 1,
     balancedParenthesesCount 2, balancedParenthesesCount 3,
     balancedParenthesesCount 4, balancedParenthesesCount 5,
     balancedParenthesesCount 6] =
    [1, 1, 2, 5, 14, 42, 132] := by native_decide

theorem balanced_same_as_dyck_small :
    balancedParenthesesCount 0 = dyckPathCount 0 ∧
    balancedParenthesesCount 1 = dyckPathCount 1 ∧
    balancedParenthesesCount 2 = dyckPathCount 2 ∧
    balancedParenthesesCount 3 = dyckPathCount 3 ∧
    balancedParenthesesCount 4 = dyckPathCount 4 ∧
    balancedParenthesesCount 5 = dyckPathCount 5 ∧
    balancedParenthesesCount 6 = dyckPathCount 6 := by native_decide

theorem balanced_small_word_counts :
    balancedParenthesesCount 0 = 1 ∧
    balancedParenthesesCount 1 = 1 ∧
    balancedParenthesesCount 2 = 2 ∧
    balancedParenthesesCount 3 = 5 := by native_decide

/-! ## 3. Series-parallel networks -/

/- Ordered two-terminal series-parallel expression trees are represented by the
large Schroeder specification `N = 1 + z N + z N^2`. -/

def seriesParallelScheme : SpecificationScheme :=
  { variableCount := 1
    equations :=
      [{ lhs := 0, rhs := [epsilonTerm, zTimes [0], zTimes [0, 0]] }] }

/-- Large Schroeder numbers, used here for ordered series-parallel schemes. -/
def seriesParallelNetworks : Nat -> Nat
  | 0 => 1
  | 1 => 2
  | n + 2 =>
      ((6 * (n + 1) + 3) * seriesParallelNetworks (n + 1) -
        n * seriesParallelNetworks n) / (n + 3)
termination_by n => n

def seriesParallelAnalysis : SquareRootAnalysis :=
  { scheme := seriesParallelScheme
    rhoLowerNumerator := 1
    rhoLowerDenominator := 6
    rhoUpperNumerator := 1
    rhoUpperDenominator := 5
    growthLowerNumerator := 5
    growthLowerDenominator := 1
    growthUpperNumerator := 6
    growthUpperDenominator := 1
    transferExponentNumerator := 3
    transferExponentDenominator := 2
    checkedCoefficients := [1, 2, 6, 22, 90, 394, 1806, 8558] }

theorem series_parallel_table :
    [seriesParallelNetworks 0, seriesParallelNetworks 1,
     seriesParallelNetworks 2, seriesParallelNetworks 3,
     seriesParallelNetworks 4, seriesParallelNetworks 5,
     seriesParallelNetworks 6, seriesParallelNetworks 7] =
    [1, 2, 6, 22, 90, 394, 1806, 8558] := by native_decide

theorem series_parallel_convolution_0_to_5 :
    seriesParallelNetworks 1 =
      seriesParallelNetworks 0 +
        (∑ k ∈ Finset.range 1,
          seriesParallelNetworks k * seriesParallelNetworks (0 - k)) ∧
    seriesParallelNetworks 2 =
      seriesParallelNetworks 1 +
        (∑ k ∈ Finset.range 2,
          seriesParallelNetworks k * seriesParallelNetworks (1 - k)) ∧
    seriesParallelNetworks 3 =
      seriesParallelNetworks 2 +
        (∑ k ∈ Finset.range 3,
          seriesParallelNetworks k * seriesParallelNetworks (2 - k)) ∧
    seriesParallelNetworks 4 =
      seriesParallelNetworks 3 +
        (∑ k ∈ Finset.range 4,
          seriesParallelNetworks k * seriesParallelNetworks (3 - k)) ∧
    seriesParallelNetworks 5 =
      seriesParallelNetworks 4 +
        (∑ k ∈ Finset.range 5,
          seriesParallelNetworks k * seriesParallelNetworks (4 - k)) ∧
    seriesParallelNetworks 6 =
      seriesParallelNetworks 5 +
        (∑ k ∈ Finset.range 6,
          seriesParallelNetworks k * seriesParallelNetworks (5 - k)) := by
  native_decide

theorem series_parallel_three_term_2_to_7 :
    3 * seriesParallelNetworks 2 + 0 * seriesParallelNetworks 0 =
      9 * seriesParallelNetworks 1 ∧
    4 * seriesParallelNetworks 3 + 1 * seriesParallelNetworks 1 =
      15 * seriesParallelNetworks 2 ∧
    5 * seriesParallelNetworks 4 + 2 * seriesParallelNetworks 2 =
      21 * seriesParallelNetworks 3 ∧
    6 * seriesParallelNetworks 5 + 3 * seriesParallelNetworks 3 =
      27 * seriesParallelNetworks 4 ∧
    7 * seriesParallelNetworks 6 + 4 * seriesParallelNetworks 4 =
      33 * seriesParallelNetworks 5 ∧
    8 * seriesParallelNetworks 7 + 5 * seriesParallelNetworks 5 =
      39 * seriesParallelNetworks 6 := by native_decide

/-! ## 4. Hierarchical sequences -/

/- Ordered rooted trees with allowed branch counts `0`, `1`, and `3`:
`T = z * (1 + T + T^3)`. -/

def hierarchicalSequenceScheme : SpecificationScheme :=
  { variableCount := 1
    equations :=
      [{ lhs := 0, rhs := [atomTerm, zTimes [0], zTimes [0, 0, 0]] }] }

def hierarchicalSequenceCount : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 5
  | 6 => 11
  | 7 => 24
  | 8 => 57
  | 9 => 141
  | _ => 0

def hierarchicalSequenceAnalysis : SquareRootAnalysis :=
  { scheme := hierarchicalSequenceScheme
    rhoLowerNumerator := 1
    rhoLowerDenominator := 3
    rhoUpperNumerator := 1
    rhoUpperDenominator := 2
    growthLowerNumerator := 2
    growthLowerDenominator := 1
    growthUpperNumerator := 3
    growthUpperDenominator := 1
    transferExponentNumerator := 3
    transferExponentDenominator := 2
    checkedCoefficients := [0, 1, 1, 1, 2, 5, 11, 24, 57, 141] }

theorem hierarchical_sequence_table :
    [hierarchicalSequenceCount 0, hierarchicalSequenceCount 1,
     hierarchicalSequenceCount 2, hierarchicalSequenceCount 3,
     hierarchicalSequenceCount 4, hierarchicalSequenceCount 5,
     hierarchicalSequenceCount 6, hierarchicalSequenceCount 7,
     hierarchicalSequenceCount 8, hierarchicalSequenceCount 9] =
    [0, 1, 1, 1, 2, 5, 11, 24, 57, 141] := by native_decide

theorem hierarchical_restricted_branching_checks :
    hierarchicalSequenceCount 1 = 1 ∧
    hierarchicalSequenceCount 2 = hierarchicalSequenceCount 1 ∧
    hierarchicalSequenceCount 3 = hierarchicalSequenceCount 2 ∧
    hierarchicalSequenceCount 4 =
      hierarchicalSequenceCount 3 +
        hierarchicalSequenceCount 1 * hierarchicalSequenceCount 1 *
          hierarchicalSequenceCount 1 ∧
    hierarchicalSequenceCount 5 =
      hierarchicalSequenceCount 4 +
        3 * hierarchicalSequenceCount 1 * hierarchicalSequenceCount 1 *
          hierarchicalSequenceCount 2 ∧
    hierarchicalSequenceCount 6 =
      hierarchicalSequenceCount 5 +
        3 * hierarchicalSequenceCount 1 * hierarchicalSequenceCount 1 *
          hierarchicalSequenceCount 3 +
        3 * hierarchicalSequenceCount 1 * hierarchicalSequenceCount 2 *
          hierarchicalSequenceCount 2 ∧
    hierarchicalSequenceCount 7 =
      hierarchicalSequenceCount 6 +
        3 * hierarchicalSequenceCount 1 * hierarchicalSequenceCount 1 *
          hierarchicalSequenceCount 4 +
        6 * hierarchicalSequenceCount 1 * hierarchicalSequenceCount 2 *
          hierarchicalSequenceCount 3 +
        hierarchicalSequenceCount 2 * hierarchicalSequenceCount 2 *
          hierarchicalSequenceCount 2 := by native_decide

/-! ## 5. Connected functional digraphs -/

/-- Rooted labelled trees: Cayley's `n^(n-1)`. -/
def cayleyRootedTrees (n : Nat) : Nat := if n = 0 then 0 else n ^ (n - 1)

/-- Contribution of cycle length `k` to connected functional digraphs on `n` labels. -/
def connectedFunctionalDigraphTerm (n k : Nat) : Nat :=
  if n = 0 || k = 0 || n < k then 0
  else (Nat.factorial n / Nat.factorial (n - k) * n ^ (n - k)) / n

/-- Connected components of functional digraphs on `n` labelled vertices. -/
def connectedFunctionalDigraphs (n : Nat) : Nat :=
  ∑ k ∈ Finset.range (n + 1), connectedFunctionalDigraphTerm n k

theorem connected_functional_digraph_table :
    [connectedFunctionalDigraphs 1, connectedFunctionalDigraphs 2,
     connectedFunctionalDigraphs 3, connectedFunctionalDigraphs 4,
     connectedFunctionalDigraphs 5, connectedFunctionalDigraphs 6,
     connectedFunctionalDigraphs 7] =
    [1, 3, 17, 142, 1569, 21576, 355081] := by native_decide

theorem connected_functional_digraph_cycle_terms_n4 :
    [connectedFunctionalDigraphTerm 4 1, connectedFunctionalDigraphTerm 4 2,
     connectedFunctionalDigraphTerm 4 3, connectedFunctionalDigraphTerm 4 4] =
    [64, 48, 24, 6] := by native_decide

theorem one_cycle_term_is_cayley_1_to_7 :
    connectedFunctionalDigraphTerm 1 1 = cayleyRootedTrees 1 ∧
    connectedFunctionalDigraphTerm 2 1 = cayleyRootedTrees 2 ∧
    connectedFunctionalDigraphTerm 3 1 = cayleyRootedTrees 3 ∧
    connectedFunctionalDigraphTerm 4 1 = cayleyRootedTrees 4 ∧
    connectedFunctionalDigraphTerm 5 1 = cayleyRootedTrees 5 ∧
    connectedFunctionalDigraphTerm 6 1 = cayleyRootedTrees 6 ∧
    connectedFunctionalDigraphTerm 7 1 = cayleyRootedTrees 7 := by native_decide

theorem cayley_rooted_values :
    [cayleyRootedTrees 1, cayleyRootedTrees 2, cayleyRootedTrees 3,
     cayleyRootedTrees 4, cayleyRootedTrees 5, cayleyRootedTrees 6,
     cayleyRootedTrees 7] =
    [1, 2, 9, 64, 625, 7776, 117649] := by native_decide

/-! ## 6. Simple varieties of labelled trees -/

/- For the labelled tree equation `T = z exp(T)`, Lagrange inversion gives
`n! [z^n] T(z) = (n - 1)! [u^(n-1)] exp(nu) = n^(n-1)`.  The scaled
exponential coefficient `m! [u^m] exp(a u)` is `a^m`. -/

def expScaledCoeff (a m : Nat) : Nat := a ^ m

def simpleTreeExponentialCoeff (n : Nat) : Nat :=
  if n = 0 then 0 else expScaledCoeff n (n - 1)

theorem exp_scaled_coeff_table :
    [expScaledCoeff 1 0, expScaledCoeff 2 1, expScaledCoeff 3 2,
     expScaledCoeff 4 3, expScaledCoeff 5 4, expScaledCoeff 6 5] =
    [1, 2, 9, 64, 625, 7776] := by native_decide

theorem simple_tree_exponential_coefficients :
    [simpleTreeExponentialCoeff 1, simpleTreeExponentialCoeff 2,
     simpleTreeExponentialCoeff 3, simpleTreeExponentialCoeff 4,
     simpleTreeExponentialCoeff 5, simpleTreeExponentialCoeff 6,
     simpleTreeExponentialCoeff 7] =
    [1, 2, 9, 64, 625, 7776, 117649] := by native_decide

theorem simple_tree_matches_cayley_1_to_7 :
    simpleTreeExponentialCoeff 1 = cayleyRootedTrees 1 ∧
    simpleTreeExponentialCoeff 2 = cayleyRootedTrees 2 ∧
    simpleTreeExponentialCoeff 3 = cayleyRootedTrees 3 ∧
    simpleTreeExponentialCoeff 4 = cayleyRootedTrees 4 ∧
    simpleTreeExponentialCoeff 5 = cayleyRootedTrees 5 ∧
    simpleTreeExponentialCoeff 6 = cayleyRootedTrees 6 ∧
    simpleTreeExponentialCoeff 7 = cayleyRootedTrees 7 := by native_decide



structure ContextFreeSchemesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ContextFreeSchemesBudgetCertificate.controlled
    (c : ContextFreeSchemesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ContextFreeSchemesBudgetCertificate.budgetControlled
    (c : ContextFreeSchemesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ContextFreeSchemesBudgetCertificate.Ready
    (c : ContextFreeSchemesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ContextFreeSchemesBudgetCertificate.size
    (c : ContextFreeSchemesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem contextFreeSchemes_budgetCertificate_le_size
    (c : ContextFreeSchemesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleContextFreeSchemesBudgetCertificate :
    ContextFreeSchemesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleContextFreeSchemesBudgetCertificate.Ready := by
  constructor
  · norm_num [ContextFreeSchemesBudgetCertificate.controlled,
      sampleContextFreeSchemesBudgetCertificate]
  · norm_num [ContextFreeSchemesBudgetCertificate.budgetControlled,
      sampleContextFreeSchemesBudgetCertificate]

example :
    sampleContextFreeSchemesBudgetCertificate.certificateBudgetWindow ≤
      sampleContextFreeSchemesBudgetCertificate.size := by
  apply contextFreeSchemes_budgetCertificate_le_size
  constructor
  · norm_num [ContextFreeSchemesBudgetCertificate.controlled,
      sampleContextFreeSchemesBudgetCertificate]
  · norm_num [ContextFreeSchemesBudgetCertificate.budgetControlled,
      sampleContextFreeSchemesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleContextFreeSchemesBudgetCertificate.Ready := by
  constructor
  · norm_num [ContextFreeSchemesBudgetCertificate.controlled,
      sampleContextFreeSchemesBudgetCertificate]
  · norm_num [ContextFreeSchemesBudgetCertificate.budgetControlled,
      sampleContextFreeSchemesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleContextFreeSchemesBudgetCertificate.certificateBudgetWindow ≤
      sampleContextFreeSchemesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ContextFreeSchemesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleContextFreeSchemesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleContextFreeSchemesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.ContextFreeSchemes
