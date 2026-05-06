import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.SupAperiodicGF


/-!
Bounded executable tables for Chapter IV themes around supercritical
composition, aperiodicity, Pringsheim witnesses, and lacunary coefficient
patterns.  These are finite windows, not analytic completeness theorems.
-/

def lookup12 (a : Fin 12 → ℕ) (n : ℕ) : ℕ :=
  if h : n < 12 then a ⟨n, h⟩ else 0

def allRange (m : ℕ) (p : ℕ → Bool) : Bool :=
  (List.range m).all p

/-! ## Supercritical sequence composition windows -/

/-- Coefficients of `1 / (1 - (z + z^2))` through degree `11`. -/
def seqParts12Coeffs : Fin 12 → ℕ :=
  ![1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144]

/-- Coefficients of `1 / (1 - (z + z^2 + z^3))` through degree `11`. -/
def seqParts123Coeffs : Fin 12 → ℕ :=
  ![1, 1, 2, 4, 7, 13, 24, 44, 81, 149, 274, 504]

/-- Coefficients of `1 / (1 - (2z + z^2))` through degree `11`. -/
def superSeqTwoOneCoeffs : Fin 12 → ℕ :=
  ![1, 2, 5, 12, 29, 70, 169, 408, 985, 2378, 5741, 13860]

def binaryPartSeqRecurrenceCheck (a : Fin 12 → ℕ) : Bool :=
  allRange 10 fun n =>
    lookup12 a (n + 2) == lookup12 a (n + 1) + lookup12 a n

def ternaryPartSeqRecurrenceCheck (a : Fin 12 → ℕ) : Bool :=
  allRange 9 fun n =>
    lookup12 a (n + 3) ==
      lookup12 a (n + 2) + lookup12 a (n + 1) + lookup12 a n

def superTwoOneRecurrenceCheck (a : Fin 12 → ℕ) : Bool :=
  allRange 10 fun n =>
    lookup12 a (n + 2) == 2 * lookup12 a (n + 1) + lookup12 a n

theorem seqParts12_recurrence :
    binaryPartSeqRecurrenceCheck seqParts12Coeffs = true := by
  native_decide

theorem seqParts123_recurrence :
    ternaryPartSeqRecurrenceCheck seqParts123Coeffs = true := by
  native_decide

theorem superSeqTwoOne_recurrence :
    superTwoOneRecurrenceCheck superSeqTwoOneCoeffs = true := by
  native_decide

theorem superSeqTwoOne_dominates_binary_window :
    ∀ n : Fin 12, seqParts12Coeffs n ≤ superSeqTwoOneCoeffs n := by
  native_decide

theorem superSeqTwoOne_strict_after_constant :
    ∀ n : Fin 11, seqParts12Coeffs ⟨n + 1, by omega⟩ <
      superSeqTwoOneCoeffs ⟨n + 1, by omega⟩ := by
  native_decide

/-! ## Aperiodicity tests for finite supports -/

/-- Support flags for `{1, 2}`, aperiodic by gcd one. -/
def support12 : Fin 12 → ℕ :=
  ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Support flags for `{2, 4, 6, 8, 10}`, periodic with span two. -/
def evenSupport : Fin 12 → ℕ :=
  ![0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

/-- Support flags for `{3, 6, 9}`, periodic with span three. -/
def tripleSupport : Fin 12 → ℕ :=
  ![0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0]

def hasPositiveAt (a : Fin 12 → ℕ) (n : ℕ) : Bool :=
  decide (0 < lookup12 a n)

def supportHasGapOne (a : Fin 12 → ℕ) : Bool :=
  (List.range 11).any fun n =>
    hasPositiveAt a n && hasPositiveAt a (n + 1)

def supportOnlyMultiplesOf (d : ℕ) (a : Fin 12 → ℕ) : Bool :=
  allRange 12 fun n =>
    decide (lookup12 a n = 0 ∨ n % d = 0)

theorem support12_has_gap_one :
    supportHasGapOne support12 = true := by
  native_decide

theorem evenSupport_only_multiples_two :
    supportOnlyMultiplesOf 2 evenSupport = true := by
  native_decide

theorem tripleSupport_only_multiples_three :
    supportOnlyMultiplesOf 3 tripleSupport = true := by
  native_decide

theorem support12_not_only_multiples_two :
    supportOnlyMultiplesOf 2 support12 = false := by
  native_decide

theorem support12_not_only_multiples_three :
    supportOnlyMultiplesOf 3 support12 = false := by
  native_decide

/-! ## Exponential growth detection tables -/

/-- Powers of two, modelling a rational GF with radius `1/2`. -/
def powersTwoCoeffs : Fin 12 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

/-- Powers of three, modelling a rational GF with radius `1/3`. -/
def powersThreeCoeffs : Fin 12 → ℕ :=
  ![1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 59049, 177147]

/-- Linear coefficients of `1 / (1 - z)^2`, not exponential on this test. -/
def linearPoleCoeffs : Fin 12 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def exactRatioCheck (q : ℕ) (a : Fin 12 → ℕ) : Bool :=
  allRange 11 fun n => lookup12 a (n + 1) == q * lookup12 a n

def eventuallyAtLeastDoubleCheck (start : ℕ) (a : Fin 12 → ℕ) : Bool :=
  allRange (11 - start) fun k =>
    let n := start + k
    decide (2 * lookup12 a n ≤ lookup12 a (n + 1))

theorem powersTwo_exact_ratio :
    exactRatioCheck 2 powersTwoCoeffs = true := by
  native_decide

theorem powersThree_exact_ratio :
    exactRatioCheck 3 powersThreeCoeffs = true := by
  native_decide

theorem powersThree_eventually_at_least_double :
    eventuallyAtLeastDoubleCheck 0 powersThreeCoeffs = true := by
  native_decide

theorem linearPole_not_exact_ratio_two :
    exactRatioCheck 2 linearPoleCoeffs = false := by
  native_decide

theorem linearPole_not_eventually_double_from_four :
    eventuallyAtLeastDoubleCheck 4 linearPoleCoeffs = false := by
  native_decide

/-! ## Dominant singularity radius tables for known rational GFs -/

/--
Integer table of inverse radii for `1 / (1 - qz)`, with `q = 1..6`;
the radius itself is `1 / q`.
-/
def geomInverseRadiusTable : Fin 6 → ℕ :=
  ![1, 2, 3, 4, 5, 6]

/--
Integer table of inverse radii for `1 / (1 - qz)^2`, with `q = 1..6`.
The pole order changes polynomial factors, not the exponential rate.
-/
def doublePoleInverseRadiusTable : Fin 6 → ℕ :=
  ![1, 2, 3, 4, 5, 6]

def inverseRadiusForIndex (n : ℕ) : ℕ :=
  n + 1

theorem geomInverseRadiusTable_formula :
    ∀ i : Fin 6, geomInverseRadiusTable i = inverseRadiusForIndex i := by
  native_decide

theorem doublePole_same_inverse_radius :
    ∀ i : Fin 6, doublePoleInverseRadiusTable i = geomInverseRadiusTable i := by
  native_decide

theorem inverse_radius_table_strictly_increases :
    ∀ i : Fin 5,
      geomInverseRadiusTable ⟨i, by omega⟩ <
        geomInverseRadiusTable ⟨i + 1, by omega⟩ := by
  native_decide

/-! ## Finite Pringsheim-style witnesses -/

def nonnegativeWindow (a : Fin 12 → ℕ) : Bool :=
  allRange 12 fun n => decide (0 ≤ lookup12 a n)

def hasPositiveCoefficientBefore (m : ℕ) (a : Fin 12 → ℕ) : Bool :=
  (List.range m).any fun n => decide (0 < lookup12 a n)

def pringsheimWitnessCheck (a : Fin 12 → ℕ) (m : ℕ) : Bool :=
  nonnegativeWindow a && hasPositiveCoefficientBefore m a

theorem powersTwo_pringsheim_witness :
    pringsheimWitnessCheck powersTwoCoeffs 12 = true := by
  native_decide

theorem seqParts123_pringsheim_witness :
    pringsheimWitnessCheck seqParts123Coeffs 12 = true := by
  native_decide

theorem evenSupport_pringsheim_witness :
    pringsheimWitnessCheck evenSupport 12 = true := by
  native_decide

/-! ## Lacunary series coefficient patterns -/

/-- Coefficients of `sum z^(2^k)` in the window `0 <= n < 12`. -/
def powerOfTwoLacunaryCoeffs : Fin 12 → ℕ :=
  ![0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0]

/-- Coefficients of `sum z^(k^2)` in the window `0 <= n < 12`. -/
def squareLacunaryCoeffs : Fin 12 → ℕ :=
  ![1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]

def isSmallPowerOfTwo (n : ℕ) : Bool :=
  n = 1 || n = 2 || n = 4 || n = 8

def isSmallSquare (n : ℕ) : Bool :=
  n = 0 || n = 1 || n = 4 || n = 9

def indicator (p : Bool) : ℕ :=
  if p then 1 else 0

theorem powerOfTwoLacunary_table :
    ∀ i : Fin 12,
      powerOfTwoLacunaryCoeffs i = indicator (isSmallPowerOfTwo i) := by
  native_decide

theorem squareLacunary_table :
    ∀ i : Fin 12,
      squareLacunaryCoeffs i = indicator (isSmallSquare i) := by
  native_decide

theorem lacunary_tables_differ_at_zero :
    squareLacunaryCoeffs 0 = 1 ∧ powerOfTwoLacunaryCoeffs 0 = 0 := by
  native_decide

theorem powerOfTwo_lacunary_has_long_gap :
    lookup12 powerOfTwoLacunaryCoeffs 5 = 0 ∧
      lookup12 powerOfTwoLacunaryCoeffs 6 = 0 ∧
      lookup12 powerOfTwoLacunaryCoeffs 7 = 0 := by
  native_decide



structure SupAperiodicGFBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SupAperiodicGFBudgetCertificate.controlled
    (c : SupAperiodicGFBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SupAperiodicGFBudgetCertificate.budgetControlled
    (c : SupAperiodicGFBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SupAperiodicGFBudgetCertificate.Ready
    (c : SupAperiodicGFBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SupAperiodicGFBudgetCertificate.size
    (c : SupAperiodicGFBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem supAperiodicGF_budgetCertificate_le_size
    (c : SupAperiodicGFBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSupAperiodicGFBudgetCertificate :
    SupAperiodicGFBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSupAperiodicGFBudgetCertificate.Ready := by
  constructor
  · norm_num [SupAperiodicGFBudgetCertificate.controlled,
      sampleSupAperiodicGFBudgetCertificate]
  · norm_num [SupAperiodicGFBudgetCertificate.budgetControlled,
      sampleSupAperiodicGFBudgetCertificate]

example :
    sampleSupAperiodicGFBudgetCertificate.certificateBudgetWindow ≤
      sampleSupAperiodicGFBudgetCertificate.size := by
  apply supAperiodicGF_budgetCertificate_le_size
  constructor
  · norm_num [SupAperiodicGFBudgetCertificate.controlled,
      sampleSupAperiodicGFBudgetCertificate]
  · norm_num [SupAperiodicGFBudgetCertificate.budgetControlled,
      sampleSupAperiodicGFBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSupAperiodicGFBudgetCertificate.Ready := by
  constructor
  · norm_num [SupAperiodicGFBudgetCertificate.controlled,
      sampleSupAperiodicGFBudgetCertificate]
  · norm_num [SupAperiodicGFBudgetCertificate.budgetControlled,
      sampleSupAperiodicGFBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSupAperiodicGFBudgetCertificate.certificateBudgetWindow ≤
      sampleSupAperiodicGFBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SupAperiodicGFBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSupAperiodicGFBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSupAperiodicGFBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.SupAperiodicGF
