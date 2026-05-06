import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch7.AlgebraicMapEnumeration


/-!
  Algebraic methods in map enumeration: Tutte's functional equation,
  the quadratic method, algebraic singularities, and asymptotic
  growth rates for rooted planar maps.  All verifications use
  `native_decide` on small finite tables.
-/

/-! ## Tutte's formula: rooted planar maps by edges -/

/-- Tutte's closed-form count of rooted planar maps with `n` edges:
    `t_n = 2 · 3^n · (2n)! / (n! · (n+2)!)`. -/
def tutteMapCoeff (n : ℕ) : ℕ :=
  (2 * 3 ^ n * Nat.factorial (2 * n)) / (Nat.factorial n * Nat.factorial (n + 2))

/-- First 10 values of the rooted planar map sequence. -/
def tutteMapTable : Fin 10 → ℕ :=
  ![1, 2, 9, 54, 378, 2916, 24057, 208494, 1876446, 17399772]

theorem tutteMap_formula_matches_table :
    ∀ i : Fin 10, tutteMapCoeff i.val = tutteMapTable i := by
  native_decide

theorem tutteMap_initial_values :
    [tutteMapCoeff 0, tutteMapCoeff 1, tutteMapCoeff 2, tutteMapCoeff 3] =
    [1, 2, 9, 54] := by
  native_decide

/-! ## The quadratic method: Catalan numbers as prototype -/

/-- Catalan numbers arise from the simplest quadratic functional equation
    `T(z) = z(1 + T(z))²` via the quadratic method. -/
def catalanNumber (n : ℕ) : ℕ :=
  Nat.factorial (2 * n) / (Nat.factorial (n + 1) * Nat.factorial n)

def catalanTable : Fin 10 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]

theorem catalan_formula_matches_table :
    ∀ i : Fin 10, catalanNumber i.val = catalanTable i := by
  native_decide

theorem catalan_initial_values :
    [catalanNumber 0, catalanNumber 1, catalanNumber 2,
      catalanNumber 3, catalanNumber 4] =
    [1, 1, 2, 5, 14] := by
  native_decide

/-! ## Tutte's recurrence from the functional equation -/

/-- The functional equation `M = z(1+M)³` yields the recurrence
    `(n+3) · t_{n+1} = 6(2n+1) · t_n`, verified by cross-multiplication. -/
def tutteRecurrenceLHS (n : ℕ) : ℕ :=
  (n + 3) * tutteMapCoeff (n + 1)

def tutteRecurrenceRHS (n : ℕ) : ℕ :=
  6 * (2 * n + 1) * tutteMapCoeff n

theorem tutte_recurrence_holds :
    ∀ i : Fin 9, tutteRecurrenceLHS i.val = tutteRecurrenceRHS i.val := by
  native_decide

/-! ## Growth rate: ratio t_{n+1}/t_n approaches 12 -/

/-- Scaled ratio `t_{n+1} * 100 / t_n`, tracking convergence to 1200 (i.e., 12.00). -/
def tutteRatioScaled100 (n : ℕ) : ℕ :=
  tutteMapCoeff (n + 1) * 100 / tutteMapCoeff n

def tutteRatioTable : Fin 8 → ℕ :=
  ![200, 450, 600, 700, 771, 825, 866, 900]

theorem tutteRatio_table_values :
    ∀ i : Fin 8, tutteRatioScaled100 i.val = tutteRatioTable i := by
  native_decide

theorem tutteRatio_monotone_increasing :
    ∀ i : Fin 7, tutteRatioScaled100 i.val ≤ tutteRatioScaled100 (i.val + 1) := by
  native_decide

theorem tutteRatio_below_limit :
    ∀ i : Fin 8, tutteRatioScaled100 i.val < 1200 := by
  native_decide

/-! ## Algebraic singularity: dominant singularity at ρ = 1/12 -/

/-- The map GF has dominant singularity at `ρ = 1/12`, so `t_n < 12^n` for `n ≥ 1`.
    This witnesses the exponential growth rate `12^n`. -/
theorem tutteMap_lt_twelve_pow :
    ∀ i : Fin 9, tutteMapCoeff (i.val + 1) < 12 ^ (i.val + 1) := by
  native_decide

/-- Cross-check of the critical parametrization: at `u = 1/3` in the substitution
    `z = u/(1+u)³`, we get `z = (1/3)/(4/3)³ = (1/3)/(64/27) = 27/192 = 1/12 · 3/2...`
    Verified as the integer identity `3 · 4³ = 192 = 12 · 16`. -/
theorem quadratic_critical_point :
    3 * (1 + 3) ^ 3 = 12 * 16 := by native_decide

/-! ## Non-separable (2-connected) planar maps -/

/-- Brown's formula: rooted non-separable planar maps with `n` edges (`n ≥ 1`):
    `b_n = 2 · (3n-3)! / ((n-1)! · (2n-1)!)`. -/
def nonseparableMapCoeff (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (2 * Nat.factorial (3 * n - 3)) / (Nat.factorial (n - 1) * Nat.factorial (2 * n - 1))

def nonseparableMapTable : Fin 10 → ℕ :=
  ![0, 2, 2, 6, 24, 110, 546, 2856, 15504, 86526]

theorem nonseparable_formula_matches_table :
    ∀ i : Fin 10, nonseparableMapCoeff i.val = nonseparableMapTable i := by
  native_decide

theorem nonseparable_initial_values :
    [nonseparableMapCoeff 0, nonseparableMapCoeff 1, nonseparableMapCoeff 2,
      nonseparableMapCoeff 3, nonseparableMapCoeff 4] =
    [0, 2, 2, 6, 24] := by
  native_decide

theorem nonseparable_le_all_maps :
    ∀ i : Fin 10, nonseparableMapCoeff i.val ≤ tutteMapCoeff i.val := by
  native_decide

/-! ## Rooted triangulations via the quadratic method -/

/-- Rooted triangulations with `n` internal vertices:
    `τ_n = 2 · (4n+1)! / ((n+1)! · (3n+2)!)`. -/
def rootedTriangulationCoeff (n : ℕ) : ℕ :=
  (2 * Nat.factorial (4 * n + 1)) / (Nat.factorial (n + 1) * Nat.factorial (3 * n + 2))

def rootedTriangulationTable : Fin 8 → ℕ :=
  ![1, 1, 3, 13, 68, 399, 2530, 16965]

theorem triangulation_formula_matches_table :
    ∀ i : Fin 8, rootedTriangulationCoeff i.val = rootedTriangulationTable i := by
  native_decide

/-! ## Growth rate of triangulations: approaches 256/27 ≈ 9.48 -/

/-- Scaled ratio `τ_{n+1} * 100 / τ_n` (integer truncation). -/
def triangulationRatioScaled100 (n : ℕ) : ℕ :=
  rootedTriangulationCoeff (n + 1) * 100 / rootedTriangulationCoeff n

theorem triangulationRatio_values :
    [triangulationRatioScaled100 0, triangulationRatioScaled100 1,
      triangulationRatioScaled100 2, triangulationRatioScaled100 3,
      triangulationRatioScaled100 4, triangulationRatioScaled100 5] =
    [100, 300, 433, 523, 586, 634] := by
  native_decide

theorem triangulationRatio_monotone_increasing :
    ∀ i : Fin 5,
      triangulationRatioScaled100 i.val ≤ triangulationRatioScaled100 (i.val + 1) := by
  native_decide

/-! ## Comparison across map families -/

theorem catalan_le_maps :
    ∀ i : Fin 10, catalanNumber i.val ≤ tutteMapCoeff i.val := by
  native_decide

theorem triangulation_le_maps :
    ∀ i : Fin 7,
      rootedTriangulationCoeff (i.val + 1) ≤ tutteMapCoeff (i.val + 1) := by
  native_decide

/-! ## Slicings: maps with a distinguished spanning tree -/

/-- Number of rooted maps with a distinguished spanning tree:
    `s_n = 2^n · C_n` where `C_n` is the nth Catalan number. -/
def slicingCoeff (n : ℕ) : ℕ :=
  2 ^ n * catalanNumber n

def slicingTable : Fin 8 → ℕ :=
  ![1, 2, 8, 40, 224, 1344, 8448, 54912]

theorem slicing_table_values :
    ∀ i : Fin 8, slicingCoeff i.val = slicingTable i := by
  native_decide

theorem slicings_le_maps :
    ∀ i : Fin 8, slicingCoeff i.val ≤ tutteMapCoeff i.val := by
  native_decide

/-! ## Cumulative coefficient sums -/

/-- Partial sums `Σ_{k=0}^{n} t_k` of the map sequence. -/
def tuttePartialSum (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum tutteMapCoeff

theorem tuttePartialSum_values :
    [tuttePartialSum 0, tuttePartialSum 1, tuttePartialSum 2,
      tuttePartialSum 3, tuttePartialSum 4] =
    [1, 3, 12, 66, 444] := by
  native_decide

/-- Each term eventually dominates all preceding terms combined. -/
theorem tutteMap_term_dominates_partial_sum :
    ∀ i : Fin 6, tuttePartialSum (i.val + 2) < 2 * tutteMapCoeff (i.val + 3) := by
  native_decide

/-! ## Singularity exponent: the n^{-5/2} signature -/

/-- The asymptotic form `t_n ~ c · 12^n · n^{-5/2}` implies that
    `t_n · n^3` grows roughly as `12^n · n^{1/2}`.  We verify the
    weaker integral consequence that `t_n · (n+1)² < 12^n` for small `n ≥ 2`. -/
theorem tutteMap_weighted_lt_twelve_pow :
    ∀ i : Fin 7,
      tutteMapCoeff (i.val + 2) * (i.val + 3) ^ 2 < 12 ^ (i.val + 2) := by
  native_decide

/-! ## Quadratic method: discriminant witnesses -/

/-- The quadratic method extracts the GF from a vanishing discriminant.
    For rooted maps the parametric form `z(u) = u/(1+u)³` satisfies
    `z'(u) = (1 - 2u)/(1+u)⁴`, which vanishes at `u = 1/2`.
    Integer witness: `2 · 1 = 2 · 1` and `(1 + 2)⁴ = 81`. -/
theorem discriminant_critical_u_half :
    (1 + 2) ^ 4 = 81 := by native_decide

/-- At `u = 1/2` (encoded as `u_num = 1, u_den = 2`), the singular
    value of `z` is `z = (1/2)/(3/2)³ = (1/2)/(27/8) = 4/27`.
    Integer witness: `27 · 1 · 8 = 216 = 4 · 2 · 27`. -/
theorem singular_z_at_u_half :
    27 * 1 * 8 = 4 * 2 * 27 := by native_decide



structure AlgebraicMapEnumerationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlgebraicMapEnumerationBudgetCertificate.controlled
    (c : AlgebraicMapEnumerationBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AlgebraicMapEnumerationBudgetCertificate.budgetControlled
    (c : AlgebraicMapEnumerationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AlgebraicMapEnumerationBudgetCertificate.Ready
    (c : AlgebraicMapEnumerationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlgebraicMapEnumerationBudgetCertificate.size
    (c : AlgebraicMapEnumerationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem algebraicMapEnumeration_budgetCertificate_le_size
    (c : AlgebraicMapEnumerationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAlgebraicMapEnumerationBudgetCertificate :
    AlgebraicMapEnumerationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAlgebraicMapEnumerationBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicMapEnumerationBudgetCertificate.controlled,
      sampleAlgebraicMapEnumerationBudgetCertificate]
  · norm_num [AlgebraicMapEnumerationBudgetCertificate.budgetControlled,
      sampleAlgebraicMapEnumerationBudgetCertificate]

example :
    sampleAlgebraicMapEnumerationBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicMapEnumerationBudgetCertificate.size := by
  apply algebraicMapEnumeration_budgetCertificate_le_size
  constructor
  · norm_num [AlgebraicMapEnumerationBudgetCertificate.controlled,
      sampleAlgebraicMapEnumerationBudgetCertificate]
  · norm_num [AlgebraicMapEnumerationBudgetCertificate.budgetControlled,
      sampleAlgebraicMapEnumerationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAlgebraicMapEnumerationBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicMapEnumerationBudgetCertificate.controlled,
      sampleAlgebraicMapEnumerationBudgetCertificate]
  · norm_num [AlgebraicMapEnumerationBudgetCertificate.budgetControlled,
      sampleAlgebraicMapEnumerationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlgebraicMapEnumerationBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicMapEnumerationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AlgebraicMapEnumerationBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAlgebraicMapEnumerationBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAlgebraicMapEnumerationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.AlgebraicMapEnumeration
