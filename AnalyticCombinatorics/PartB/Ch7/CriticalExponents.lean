import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch7.CriticalExponents


/-!
  Chapter VII finite checks: critical exponents and universality tables.

  The file records bounded numerical data associated with algebraic
  singularities, tree-like square-root laws, and rooted planar maps.
  The analytic asymptotic statements are represented by executable finite
  tables and small consistency checks.
-/

/-! ## Critical exponent tables -/

/--
Index convention for the exponent tables:

* 0: Catalan / binary-tree algebraic singularity.
* 1: generic Drmota-Lalley-Woods square-root schema.
* 2: subcritical vertex-counted graph family.
* 3: rooted planar maps.
* 4: higher algebraic map-type schema.
-/
def classCode : Fin 5 → ℕ := ![0, 1, 2, 3, 4]

/-- Numerators of singular exponents, with common denominator `2`. -/
def singularExponentNum : Fin 5 → ℕ := ![1, 1, 3, 3, 5]

/-- Numerators of coefficient decay exponents, with common denominator `2`. -/
def coefficientExponentNum : Fin 5 → ℕ := ![3, 3, 5, 5, 7]

/-- Common exponent denominators. -/
def exponentDen : Fin 5 → ℕ := ![2, 2, 2, 2, 2]

theorem classCode_identity : ∀ i : Fin 5, classCode i = i.val := by
  native_decide

theorem exponentDen_all_two : ∀ i : Fin 5, exponentDen i = 2 := by
  native_decide

/-- Transfer shift: a singular term with exponent `a/2` gives coefficient
decay exponent `(a+2)/2` in these table rows. -/
theorem coefficientExponent_transfer_shift :
    ∀ i : Fin 5, coefficientExponentNum i = singularExponentNum i + exponentDen i := by
  native_decide

theorem catalan_singular_alpha_half :
    singularExponentNum 0 = 1 ∧ exponentDen 0 = 2 := by
  native_decide

theorem maps_coefficient_alpha_five_halves :
    coefficientExponentNum 3 = 5 ∧ exponentDen 3 = 2 := by
  native_decide

theorem subcritical_graphs_coefficient_alpha_five_halves :
    coefficientExponentNum 2 = 5 ∧ exponentDen 2 = 2 := by
  native_decide

/-! ## Catalan coefficients -/

/-- Catalan numbers by the closed form `C_n = (2n choose n)/(n+1)`. -/
def catalanCount (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Exact Catalan coefficients `C_0, ..., C_11`. -/
def catalanTable : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786]

theorem catalan_formula_matches_table :
    ∀ n : Fin 12, catalanCount n.val = catalanTable n := by
  native_decide

theorem catalan_table_initial_block :
    catalanTable 0 = 1 ∧
    catalanTable 1 = 1 ∧
    catalanTable 2 = 2 ∧
    catalanTable 3 = 5 ∧
    catalanTable 4 = 14 ∧
    catalanTable 5 = 42 := by
  native_decide

theorem catalan_table_strict_after_one :
    catalanTable 1 < catalanTable 2 ∧
    catalanTable 2 < catalanTable 3 ∧
    catalanTable 3 < catalanTable 4 ∧
    catalanTable 4 < catalanTable 5 ∧
    catalanTable 5 < catalanTable 6 ∧
    catalanTable 6 < catalanTable 7 ∧
    catalanTable 7 < catalanTable 8 ∧
    catalanTable 8 < catalanTable 9 ∧
    catalanTable 9 < catalanTable 10 ∧
    catalanTable 10 < catalanTable 11 := by
  native_decide

/-! ## DLW square-root schema: Motzkin-type coefficients -/

/-- Motzkin coefficients `M_0, ..., M_11` as a small DLW-type table. -/
def dlwMotzkinTable : Fin 12 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, 5798]

theorem dlwMotzkin_initial_values :
    dlwMotzkinTable 0 = 1 ∧
    dlwMotzkinTable 1 = 1 ∧
    dlwMotzkinTable 2 = 2 ∧
    dlwMotzkinTable 3 = 4 ∧
    dlwMotzkinTable 4 = 9 ∧
    dlwMotzkinTable 5 = 21 := by
  native_decide

theorem dlwMotzkin_lt_three_pow :
    dlwMotzkinTable 1 < 3 ^ 1 ∧
    dlwMotzkinTable 2 < 3 ^ 2 ∧
    dlwMotzkinTable 3 < 3 ^ 3 ∧
    dlwMotzkinTable 4 < 3 ^ 4 ∧
    dlwMotzkinTable 5 < 3 ^ 5 ∧
    dlwMotzkinTable 6 < 3 ^ 6 ∧
    dlwMotzkinTable 7 < 3 ^ 7 ∧
    dlwMotzkinTable 8 < 3 ^ 8 ∧
    dlwMotzkinTable 9 < 3 ^ 9 ∧
    dlwMotzkinTable 10 < 3 ^ 10 ∧
    dlwMotzkinTable 11 < 3 ^ 11 := by
  native_decide

theorem dlwMotzkin_above_two_pow_tail :
    2 ^ 8 < dlwMotzkinTable 8 ∧
    2 ^ 9 < dlwMotzkinTable 9 ∧
    2 ^ 10 < dlwMotzkinTable 10 ∧
    2 ^ 11 < dlwMotzkinTable 11 := by
  native_decide

/-! ## Subcritical vertex-counted graph family: rooted forests -/

/-- Labelled rooted forests on `n` vertices: `(n+1)^(n-1)`. -/
def rootedForestVertexCount (n : ℕ) : ℕ :=
  (n + 1) ^ (n - 1)

/-- Rooted forest vertex counts for `n = 0, ..., 11`. -/
def rootedForestVertexTable : Fin 12 → ℕ :=
  ![1, 1, 3, 16, 125, 1296, 16807, 262144,
    4782969, 100000000, 2357947691, 61917364224]

theorem rootedForest_formula_matches_table :
    ∀ n : Fin 12, rootedForestVertexCount n.val = rootedForestVertexTable n := by
  native_decide

theorem rootedForest_contains_rooted_trees_small :
    1 ^ 0 ≤ rootedForestVertexTable 1 ∧
    2 ^ 1 ≤ rootedForestVertexTable 2 ∧
    3 ^ 2 ≤ rootedForestVertexTable 3 ∧
    4 ^ 3 ≤ rootedForestVertexTable 4 ∧
    5 ^ 4 ≤ rootedForestVertexTable 5 ∧
    6 ^ 5 ≤ rootedForestVertexTable 6 := by
  native_decide

/-! ## Rooted planar map counts -/

/-- Rooted planar maps with `n` edges:
`2 * (2n)! * 3^n / (n! * (n+2)!)`. -/
def rootedPlanarMapCount (n : ℕ) : ℕ :=
  2 * Nat.factorial (2 * n) * 3 ^ n /
    (Nat.factorial n * Nat.factorial (n + 2))

/-- Exact rooted planar map counts for `n = 0, ..., 11` edges. -/
def rootedPlanarMapTable : Fin 12 → ℕ :=
  ![1, 2, 9, 54, 378, 2916, 24057, 208494,
    1876446, 17399772, 165297834, 1602117468]

theorem rootedPlanarMap_formula_matches_table :
    ∀ n : Fin 12, rootedPlanarMapCount n.val = rootedPlanarMapTable n := by
  native_decide

theorem rootedPlanarMap_initial_values :
    rootedPlanarMapTable 0 = 1 ∧
    rootedPlanarMapTable 1 = 2 ∧
    rootedPlanarMapTable 2 = 9 ∧
    rootedPlanarMapTable 3 = 54 ∧
    rootedPlanarMapTable 4 = 378 ∧
    rootedPlanarMapTable 5 = 2916 := by
  native_decide

theorem rootedPlanarMap_dominates_catalan :
    catalanTable 0 ≤ rootedPlanarMapTable 0 ∧
    catalanTable 1 ≤ rootedPlanarMapTable 1 ∧
    catalanTable 2 ≤ rootedPlanarMapTable 2 ∧
    catalanTable 3 ≤ rootedPlanarMapTable 3 ∧
    catalanTable 4 ≤ rootedPlanarMapTable 4 ∧
    catalanTable 5 ≤ rootedPlanarMapTable 5 ∧
    catalanTable 6 ≤ rootedPlanarMapTable 6 ∧
    catalanTable 7 ≤ rootedPlanarMapTable 7 ∧
    catalanTable 8 ≤ rootedPlanarMapTable 8 ∧
    catalanTable 9 ≤ rootedPlanarMapTable 9 ∧
    catalanTable 10 ≤ rootedPlanarMapTable 10 ∧
    catalanTable 11 ≤ rootedPlanarMapTable 11 := by
  native_decide

theorem rootedPlanarMap_strictly_increases :
    rootedPlanarMapTable 0 < rootedPlanarMapTable 1 ∧
    rootedPlanarMapTable 1 < rootedPlanarMapTable 2 ∧
    rootedPlanarMapTable 2 < rootedPlanarMapTable 3 ∧
    rootedPlanarMapTable 3 < rootedPlanarMapTable 4 ∧
    rootedPlanarMapTable 4 < rootedPlanarMapTable 5 ∧
    rootedPlanarMapTable 5 < rootedPlanarMapTable 6 ∧
    rootedPlanarMapTable 6 < rootedPlanarMapTable 7 ∧
    rootedPlanarMapTable 7 < rootedPlanarMapTable 8 ∧
    rootedPlanarMapTable 8 < rootedPlanarMapTable 9 ∧
    rootedPlanarMapTable 9 < rootedPlanarMapTable 10 ∧
    rootedPlanarMapTable 10 < rootedPlanarMapTable 11 := by
  native_decide



structure CriticalExponentsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CriticalExponentsBudgetCertificate.controlled
    (c : CriticalExponentsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CriticalExponentsBudgetCertificate.budgetControlled
    (c : CriticalExponentsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CriticalExponentsBudgetCertificate.Ready
    (c : CriticalExponentsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CriticalExponentsBudgetCertificate.size
    (c : CriticalExponentsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem criticalExponents_budgetCertificate_le_size
    (c : CriticalExponentsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCriticalExponentsBudgetCertificate :
    CriticalExponentsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCriticalExponentsBudgetCertificate.Ready := by
  constructor
  · norm_num [CriticalExponentsBudgetCertificate.controlled,
      sampleCriticalExponentsBudgetCertificate]
  · norm_num [CriticalExponentsBudgetCertificate.budgetControlled,
      sampleCriticalExponentsBudgetCertificate]

example :
    sampleCriticalExponentsBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalExponentsBudgetCertificate.size := by
  apply criticalExponents_budgetCertificate_le_size
  constructor
  · norm_num [CriticalExponentsBudgetCertificate.controlled,
      sampleCriticalExponentsBudgetCertificate]
  · norm_num [CriticalExponentsBudgetCertificate.budgetControlled,
      sampleCriticalExponentsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCriticalExponentsBudgetCertificate.Ready := by
  constructor
  · norm_num [CriticalExponentsBudgetCertificate.controlled,
      sampleCriticalExponentsBudgetCertificate]
  · norm_num [CriticalExponentsBudgetCertificate.budgetControlled,
      sampleCriticalExponentsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCriticalExponentsBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalExponentsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CriticalExponentsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCriticalExponentsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCriticalExponentsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.CriticalExponents
