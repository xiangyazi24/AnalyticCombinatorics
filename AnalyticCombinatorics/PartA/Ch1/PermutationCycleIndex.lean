import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.PermutationCycleIndex


open Finset

/-!
Cycle index polynomials and Burnside/Pólya counting, matching the finite
checks in Chapter I of Analytic Combinatorics.
-/

/-- Euler's totient function, written as `φ` in the formulas below. -/
def phi (n : ℕ) : ℕ :=
  Nat.totient n

/--
Burnside fixed-point average:

`|orbits| = (1 / |G|) * ∑ g : G, |Fix(g)|`.

The input is the finite table of fixed-point counts indexed by the group
elements.
-/
def burnsideOrbitCount {groupSize : ℕ} (fixedPoints : Fin groupSize → ℕ) : ℕ :=
  (∑ g : Fin groupSize, fixedPoints g) / groupSize

/-- Rotations of a binary 4-necklace have fixed-point counts `16, 2, 4, 2`. -/
def c4BinaryFixedPoints : Fin 4 → ℕ :=
  ![16, 2, 4, 2]

theorem burnside_c4_binary_necklaces :
    burnsideOrbitCount c4BinaryFixedPoints = 6 := by
  native_decide

theorem burnside_c4_binary_fixed_sum :
    (∑ g : Fin 4, c4BinaryFixedPoints g) = 24 := by
  native_decide

/-- Pólya/Burnside numerator for `k`-colored necklaces with `n` beads. -/
def necklaceNumerator (n k : ℕ) : ℕ :=
  ∑ d ∈ Nat.divisors n, phi d * k ^ (n / d)

/--
Number of `k`-colored necklaces with `n` beads:

`necklaces(n,k) = (1/n) * ∑_{d | n} φ(d) * k^(n/d)`.
-/
def necklaces (n k : ℕ) : ℕ :=
  if n = 0 then 0 else necklaceNumerator n k / n

theorem necklace_four_two_divisor_expansion :
    necklaces 4 2 =
      (phi 1 * 2 ^ 4 + phi 2 * 2 ^ 2 + phi 4 * 2 ^ 1) / 4 := by
  native_decide

theorem necklace_four_two_numerator :
    phi 1 * 2 ^ 4 + phi 2 * 2 ^ 2 + phi 4 * 2 ^ 1 = 24 := by
  native_decide

theorem necklace_four_two_value :
    necklaces 4 2 = 6 := by
  native_decide

theorem phi_one_two_four :
    (phi 1, phi 2, phi 4) = (1, 1, 2) := by
  native_decide

/-- Checked values of `necklaces(1,k) = k`, for `k = 0, ..., 7`. -/
def necklacesOneColorTable : Fin 8 → ℕ :=
  fun k => necklaces 1 k.val

def necklacesOneColorExpected : Fin 8 → ℕ :=
  ![0, 1, 2, 3, 4, 5, 6, 7]

theorem necklaces_one_color_table :
    necklacesOneColorTable = necklacesOneColorExpected := by
  native_decide

/-- Binary necklace counts for `n = 1, ..., 6`. -/
def binaryNecklaceTable : Fin 6 → ℕ :=
  fun i => necklaces (i.val + 1) 2

def binaryNecklaceExpected : Fin 6 → ℕ :=
  ![2, 3, 4, 6, 8, 14]

theorem binary_necklace_table :
    binaryNecklaceTable = binaryNecklaceExpected := by
  native_decide

theorem necklaces_two_two :
    necklaces 2 2 = 3 := by
  native_decide

theorem necklaces_three_two :
    necklaces 3 2 = 4 := by
  native_decide

theorem necklaces_five_two :
    necklaces 5 2 = 8 := by
  native_decide

theorem necklaces_six_two :
    necklaces 6 2 = 14 := by
  native_decide

/--
Reflection fixed-point contribution for bracelets.

For odd `n`, every reflection fixes `k^((n+1)/2)` colorings.
For even `n`, half the reflections fix `k^(n/2)` colorings and half fix
`k^(n/2+1)` colorings.
-/
def braceletReflectionFixedSum (n k : ℕ) : ℕ :=
  if n % 2 = 1 then
    n * k ^ ((n + 1) / 2)
  else
    (n / 2) * (k ^ (n / 2) + k ^ (n / 2 + 1))

/-- Total Burnside numerator for dihedral bracelets. -/
def braceletNumerator (n k : ℕ) : ℕ :=
  necklaceNumerator n k + braceletReflectionFixedSum n k

/-- Number of `k`-colored bracelets with `n` beads, with flips allowed. -/
def bracelets (n k : ℕ) : ℕ :=
  if n = 0 then 0 else braceletNumerator n k / (2 * n)

theorem bracelet_odd_reflection_formula_three_two :
    braceletReflectionFixedSum 3 2 = 3 * 2 ^ ((3 + 1) / 2) := by
  native_decide

theorem bracelet_odd_reflection_formula_five_two :
    braceletReflectionFixedSum 5 2 = 5 * 2 ^ ((5 + 1) / 2) := by
  native_decide

theorem bracelet_even_reflection_formula_four_two :
    braceletReflectionFixedSum 4 2 =
      (4 / 2) * (2 ^ (4 / 2) + 2 ^ (4 / 2 + 1)) := by
  native_decide

theorem bracelet_even_reflection_formula_six_two :
    braceletReflectionFixedSum 6 2 =
      (6 / 2) * (2 ^ (6 / 2) + 2 ^ (6 / 2 + 1)) := by
  native_decide

/-- Binary bracelet counts for `n = 1, ..., 6`. -/
def binaryBraceletTable : Fin 6 → ℕ :=
  fun i => bracelets (i.val + 1) 2

def binaryBraceletExpected : Fin 6 → ℕ :=
  ![2, 3, 4, 6, 8, 13]

theorem binary_bracelet_table :
    binaryBraceletTable = binaryBraceletExpected := by
  native_decide

theorem bracelets_one_to_six_binary :
    (bracelets 1 2, bracelets 2 2, bracelets 3 2,
      bracelets 4 2, bracelets 5 2, bracelets 6 2) =
    (2, 3, 4, 6, 8, 13) := by
  native_decide

/-- `Z(S_1) = x_1`. -/
def cycleIndexS1 (x1 : ℕ) : ℕ :=
  x1

/-- `Z(S_2) = (x_1^2 + x_2) / 2`. -/
def cycleIndexS2 (x1 x2 : ℕ) : ℕ :=
  (x1 ^ 2 + x2) / 2

/-- `Z(S_3) = (x_1^3 + 3*x_1*x_2 + 2*x_3) / 6`. -/
def cycleIndexS3 (x1 x2 x3 : ℕ) : ℕ :=
  (x1 ^ 3 + 3 * x1 * x2 + 2 * x3) / 6

theorem cycle_index_s1_sample :
    cycleIndexS1 5 = 5 := by
  native_decide

theorem cycle_index_s2_polynomial_sample :
    cycleIndexS2 3 5 = (3 ^ 2 + 5) / 2 := by
  native_decide

theorem cycle_index_s3_polynomial_sample :
    cycleIndexS3 2 3 7 = (2 ^ 3 + 3 * 2 * 3 + 2 * 7) / 6 := by
  native_decide

/-- Substituting `x_i = k` into `Z(S_1)`. -/
def cycleIndexS1AtColors (k : ℕ) : ℕ :=
  cycleIndexS1 k

/-- Substituting `x_i = k` into `Z(S_2)`. -/
def cycleIndexS2AtColors (k : ℕ) : ℕ :=
  cycleIndexS2 k k

/-- Substituting `x_i = k` into `Z(S_3)`. -/
def cycleIndexS3AtColors (k : ℕ) : ℕ :=
  cycleIndexS3 k k k

def multisetSize1FromColors (k : ℕ) : ℕ :=
  k

def multisetSize2FromColors (k : ℕ) : ℕ :=
  k * (k + 1) / 2

def multisetSize3FromColors (k : ℕ) : ℕ :=
  k * (k + 1) * (k + 2) / 6

/-- Substitution checks for `k = 0, ..., 7`: `Z(S_1)(k,k,...) = k`. -/
def cycleIndexS1SubstitutionTable : Fin 8 → ℕ :=
  fun k => cycleIndexS1AtColors k.val

def multisetSize1Expected : Fin 8 → ℕ :=
  fun k => multisetSize1FromColors k.val

theorem cycle_index_s1_substitution_table :
    cycleIndexS1SubstitutionTable = multisetSize1Expected := by
  native_decide

/-- Substitution checks for `k = 0, ..., 7`: `Z(S_2)(k,k,...) = k(k+1)/2`. -/
def cycleIndexS2SubstitutionTable : Fin 8 → ℕ :=
  fun k => cycleIndexS2AtColors k.val

def multisetSize2Expected : Fin 8 → ℕ :=
  fun k => multisetSize2FromColors k.val

theorem cycle_index_s2_substitution_table :
    cycleIndexS2SubstitutionTable = multisetSize2Expected := by
  native_decide

/-- Substitution checks for `k = 0, ..., 7`: `Z(S_3)(k,k,...) = k(k+1)(k+2)/6`. -/
def cycleIndexS3SubstitutionTable : Fin 8 → ℕ :=
  fun k => cycleIndexS3AtColors k.val

def multisetSize3Expected : Fin 8 → ℕ :=
  fun k => multisetSize3FromColors k.val

theorem cycle_index_s3_substitution_table :
    cycleIndexS3SubstitutionTable = multisetSize3Expected := by
  native_decide

theorem cycle_index_binary_multiset_values :
    (cycleIndexS1AtColors 2, cycleIndexS2AtColors 2, cycleIndexS3AtColors 2) =
      (2, 3, 4) := by
  native_decide



structure PermutationCycleIndexBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PermutationCycleIndexBudgetCertificate.controlled
    (c : PermutationCycleIndexBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PermutationCycleIndexBudgetCertificate.budgetControlled
    (c : PermutationCycleIndexBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PermutationCycleIndexBudgetCertificate.Ready
    (c : PermutationCycleIndexBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PermutationCycleIndexBudgetCertificate.size
    (c : PermutationCycleIndexBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem permutationCycleIndex_budgetCertificate_le_size
    (c : PermutationCycleIndexBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePermutationCycleIndexBudgetCertificate :
    PermutationCycleIndexBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePermutationCycleIndexBudgetCertificate.Ready := by
  constructor
  · norm_num [PermutationCycleIndexBudgetCertificate.controlled,
      samplePermutationCycleIndexBudgetCertificate]
  · norm_num [PermutationCycleIndexBudgetCertificate.budgetControlled,
      samplePermutationCycleIndexBudgetCertificate]

example :
    samplePermutationCycleIndexBudgetCertificate.certificateBudgetWindow ≤
      samplePermutationCycleIndexBudgetCertificate.size := by
  apply permutationCycleIndex_budgetCertificate_le_size
  constructor
  · norm_num [PermutationCycleIndexBudgetCertificate.controlled,
      samplePermutationCycleIndexBudgetCertificate]
  · norm_num [PermutationCycleIndexBudgetCertificate.budgetControlled,
      samplePermutationCycleIndexBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePermutationCycleIndexBudgetCertificate.Ready := by
  constructor
  · norm_num [PermutationCycleIndexBudgetCertificate.controlled,
      samplePermutationCycleIndexBudgetCertificate]
  · norm_num [PermutationCycleIndexBudgetCertificate.budgetControlled,
      samplePermutationCycleIndexBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePermutationCycleIndexBudgetCertificate.certificateBudgetWindow ≤
      samplePermutationCycleIndexBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PermutationCycleIndexBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePermutationCycleIndexBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePermutationCycleIndexBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.PermutationCycleIndex
