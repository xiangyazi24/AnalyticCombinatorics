/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Asymptotic series and enumeration verifications.

  Numerical verifications of asymptotic sequences and specific enumeration
  results from Ch VII of Flajolet & Sedgewick (applications of singularity
  analysis).  All proofs are by `native_decide` on finite certificate goals.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch7.AsymptoticSeries
/-! ## 1. Binary tree enumeration — Catalan numbers

  C_n = C(2n, n) / (n + 1).  The asymptotic statement
  `C_n ~ 4^n / (√π · n^{3/2})` is not proved here; we record
  the exact values for n = 0 … 10 and the recurrence that encodes
  the growth constant ρ = 4.
-/

/-- Catalan number via the ballot formula `C(2n, n) / (n + 1)`. -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

theorem catalan_0 : catalan 0 = 1     := by native_decide
theorem catalan_1 : catalan 1 = 1     := by native_decide
theorem catalan_2 : catalan 2 = 2     := by native_decide
theorem catalan_3 : catalan 3 = 5     := by native_decide
theorem catalan_4 : catalan 4 = 14    := by native_decide
theorem catalan_5 : catalan 5 = 42    := by native_decide
theorem catalan_6 : catalan 6 = 132   := by native_decide
theorem catalan_7 : catalan 7 = 429   := by native_decide
theorem catalan_8 : catalan 8 = 1430  := by native_decide
theorem catalan_9 : catalan 9 = 4862  := by native_decide
theorem catalan_10 : catalan 10 = 16796 := by native_decide

/-! ### Catalan recurrence encoding the growth constant 4

  The identity `(n + 2) * C_{n+1} = (4n + 2) * C_n` is an integer
  reformulation of `C_{n+1}/C_n → 4`.  We verify it for n = 0 … 8.
-/

theorem catalan_rec_0 : (0 + 2) * catalan 1 = (4 * 0 + 2) * catalan 0 := by native_decide
theorem catalan_rec_1 : (1 + 2) * catalan 2 = (4 * 1 + 2) * catalan 1 := by native_decide
theorem catalan_rec_2 : (2 + 2) * catalan 3 = (4 * 2 + 2) * catalan 2 := by native_decide
theorem catalan_rec_3 : (3 + 2) * catalan 4 = (4 * 3 + 2) * catalan 3 := by native_decide
theorem catalan_rec_4 : (4 + 2) * catalan 5 = (4 * 4 + 2) * catalan 4 := by native_decide
theorem catalan_rec_5 : (5 + 2) * catalan 6 = (4 * 5 + 2) * catalan 5 := by native_decide
theorem catalan_rec_6 : (6 + 2) * catalan 7 = (4 * 6 + 2) * catalan 6 := by native_decide
theorem catalan_rec_7 : (7 + 2) * catalan 8 = (4 * 7 + 2) * catalan 7 := by native_decide
theorem catalan_rec_8 : (8 + 2) * catalan 9 = (4 * 8 + 2) * catalan 8 := by native_decide

/-! ### Cross-multiplied ratio check

  An equivalent phrasing: `catalan(n+1) * (n+2) = catalan(n) * (4*n+2)`.
  Verified for n = 0 … 8 via the ratio-check formulation.
-/

theorem catalan_ratio_0 : catalan 1 * (0 + 2) = catalan 0 * (4 * 0 + 2) := by native_decide
theorem catalan_ratio_1 : catalan 2 * (1 + 2) = catalan 1 * (4 * 1 + 2) := by native_decide
theorem catalan_ratio_2 : catalan 3 * (2 + 2) = catalan 2 * (4 * 2 + 2) := by native_decide
theorem catalan_ratio_3 : catalan 4 * (3 + 2) = catalan 3 * (4 * 3 + 2) := by native_decide
theorem catalan_ratio_4 : catalan 5 * (4 + 2) = catalan 4 * (4 * 4 + 2) := by native_decide
theorem catalan_ratio_5 : catalan 6 * (5 + 2) = catalan 5 * (4 * 5 + 2) := by native_decide
theorem catalan_ratio_6 : catalan 7 * (6 + 2) = catalan 6 * (4 * 6 + 2) := by native_decide
theorem catalan_ratio_7 : catalan 8 * (7 + 2) = catalan 7 * (4 * 7 + 2) := by native_decide
theorem catalan_ratio_8 : catalan 9 * (8 + 2) = catalan 8 * (4 * 8 + 2) := by native_decide

/-! ## 2. Ordered trees by number of leaves — Narayana numbers

  The Narayana number N(n, k) counts ordered trees with n edges and k leaves
  (equivalently, non-crossing partitions, Dyck paths with k peaks, etc.):
      N(n, k) = C(n, k) * C(n, k-1) / n   (n ≥ 1, 1 ≤ k ≤ n).

  Row sums satisfy Σ_{k=1}^{n} N(n,k) = C_n (the n-th Catalan number).
-/

/-- Narayana number N(n, k). -/
def narayanaSafe (n k : ℕ) : ℕ :=
  if n = 0 then (if k = 0 then 1 else 0)
  else if k = 0 || k > n then 0
  else Nat.choose n k * Nat.choose n (k - 1) / n

-- Individual values
theorem narayana_3_1 : narayanaSafe 3 1 = 1  := by native_decide
theorem narayana_3_2 : narayanaSafe 3 2 = 3  := by native_decide
theorem narayana_3_3 : narayanaSafe 3 3 = 1  := by native_decide
theorem narayana_4_1 : narayanaSafe 4 1 = 1  := by native_decide
theorem narayana_4_2 : narayanaSafe 4 2 = 6  := by native_decide
theorem narayana_4_3 : narayanaSafe 4 3 = 6  := by native_decide
theorem narayana_4_4 : narayanaSafe 4 4 = 1  := by native_decide
theorem narayana_5_1 : narayanaSafe 5 1 = 1  := by native_decide
theorem narayana_5_2 : narayanaSafe 5 2 = 10 := by native_decide
theorem narayana_5_3 : narayanaSafe 5 3 = 20 := by native_decide
theorem narayana_5_4 : narayanaSafe 5 4 = 10 := by native_decide
theorem narayana_5_5 : narayanaSafe 5 5 = 1  := by native_decide

/-- Row sum for n = 3: Σ N(3, k) = C_3 = 5. -/
theorem narayana_row_sum_3 :
    narayanaSafe 3 1 + narayanaSafe 3 2 + narayanaSafe 3 3 = catalan 3 := by native_decide

/-- Row sum for n = 4: Σ N(4, k) = C_4 = 14. -/
theorem narayana_row_sum_4 :
    narayanaSafe 4 1 + narayanaSafe 4 2 + narayanaSafe 4 3 + narayanaSafe 4 4 =
    catalan 4 := by native_decide

/-- Row sum for n = 5: Σ N(5, k) = C_5 = 42. -/
theorem narayana_row_sum_5 :
    narayanaSafe 5 1 + narayanaSafe 5 2 + narayanaSafe 5 3 +
    narayanaSafe 5 4 + narayanaSafe 5 5 = catalan 5 := by native_decide

/-! ## 3. Ternary trees — Fuss–Catalan family

  Ternary plane trees (each internal node has exactly 3 children) with n
  internal nodes are counted by
      T_n = C(3n, n) / (2n + 1).
-/

/-- Ternary tree count `C(3n, n) / (2n + 1)`. -/
def ternaryTree (n : ℕ) : ℕ := Nat.choose (3 * n) n / (2 * n + 1)

theorem ternaryTree_0 : ternaryTree 0 = 1   := by native_decide
theorem ternaryTree_1 : ternaryTree 1 = 1   := by native_decide
theorem ternaryTree_2 : ternaryTree 2 = 3   := by native_decide
theorem ternaryTree_3 : ternaryTree 3 = 12  := by native_decide
theorem ternaryTree_4 : ternaryTree 4 = 55  := by native_decide
theorem ternaryTree_5 : ternaryTree 5 = 273 := by native_decide

-- Spot-checks from the description
/-- `T_3 = C(9,3)/7 = 84/7 = 12`. -/
example : Nat.choose (3 * 3) 3 / (2 * 3 + 1) = 12 := by native_decide

/-- `T_4 = C(12,4)/9 = 495/9 = 55`. -/
example : Nat.choose (3 * 4) 4 / (2 * 4 + 1) = 55 := by native_decide

/-! ## 4. Fuss–Catalan numbers

  The generalised Catalan / Fuss–Catalan number
      A_p(n) = C(p·n, n) / ((p-1)·n + 1)
  counts p-ary trees with n internal nodes.  For p = 2 it reduces to the
  ordinary Catalan number, and for p = 3 to the ternary tree count.
-/

/-- Fuss–Catalan number A_p(n) = C(p*n, n) / ((p-1)*n + 1). -/
def fussCatalan (p n : ℕ) : ℕ := Nat.choose (p * n) n / ((p - 1) * n + 1)

-- For p = 2 we recover the Catalan numbers
theorem fussCatalan_2_eq_catalan_0 : fussCatalan 2 0 = catalan 0 := by native_decide
theorem fussCatalan_2_eq_catalan_1 : fussCatalan 2 1 = catalan 1 := by native_decide
theorem fussCatalan_2_eq_catalan_2 : fussCatalan 2 2 = catalan 2 := by native_decide
theorem fussCatalan_2_eq_catalan_3 : fussCatalan 2 3 = catalan 3 := by native_decide
theorem fussCatalan_2_eq_catalan_4 : fussCatalan 2 4 = catalan 4 := by native_decide
theorem fussCatalan_2_eq_catalan_5 : fussCatalan 2 5 = catalan 5 := by native_decide
theorem fussCatalan_2_eq_catalan_6 : fussCatalan 2 6 = catalan 6 := by native_decide
theorem fussCatalan_2_eq_catalan_7 : fussCatalan 2 7 = catalan 7 := by native_decide

-- For p = 3 we recover the ternary tree counts
theorem fussCatalan_3_eq_ternary_0 : fussCatalan 3 0 = ternaryTree 0 := by native_decide
theorem fussCatalan_3_eq_ternary_1 : fussCatalan 3 1 = ternaryTree 1 := by native_decide
theorem fussCatalan_3_eq_ternary_2 : fussCatalan 3 2 = ternaryTree 2 := by native_decide
theorem fussCatalan_3_eq_ternary_3 : fussCatalan 3 3 = ternaryTree 3 := by native_decide
theorem fussCatalan_3_eq_ternary_4 : fussCatalan 3 4 = ternaryTree 4 := by native_decide
theorem fussCatalan_3_eq_ternary_5 : fussCatalan 3 5 = ternaryTree 5 := by native_decide

-- p = 4 explicit values
theorem fussCatalan_4_0 : fussCatalan 4 0 = 1  := by native_decide
theorem fussCatalan_4_1 : fussCatalan 4 1 = 1  := by native_decide
/-- `A_4(2) = C(8,2)/7 = 28/7 = 4`. -/
theorem fussCatalan_4_2 : fussCatalan 4 2 = 4  := by native_decide
/-- `A_4(3) = C(12,3)/10 = 220/10 = 22`. -/
theorem fussCatalan_4_3 : fussCatalan 4 3 = 22 := by native_decide
theorem fussCatalan_4_4 : fussCatalan 4 4 = 140 := by native_decide

/-! ## 5. Ballot numbers / lattice path counts

  The number of lattice paths from (0, 0) to (n, k) using ±1 steps is
      C(n, (n + k) / 2)   when n + k is even and 0 ≤ k ≤ n,
  and 0 otherwise.
-/

/-- Ballot / lattice path count. -/
def latticePaths (n k : ℕ) : ℕ :=
  if (n + k) % 2 = 0 then Nat.choose n ((n + k) / 2) else 0

/-- `L(4, 0) = C(4, 2) = 6`. -/
theorem latticePaths_4_0 : latticePaths 4 0 = 6  := by native_decide

/-- `L(4, 2) = C(4, 3) = 4`. -/
theorem latticePaths_4_2 : latticePaths 4 2 = 4  := by native_decide

/-- `L(4, 4) = C(4, 4) = 1`. -/
theorem latticePaths_4_4 : latticePaths 4 4 = 1  := by native_decide

/-- `L(5, 1) = C(5, 3) = 10`. -/
theorem latticePaths_5_1 : latticePaths 5 1 = 10 := by native_decide

-- Additional spot-checks
theorem latticePaths_6_0 : latticePaths 6 0 = 20 := by native_decide
theorem latticePaths_6_2 : latticePaths 6 2 = 15 := by native_decide
theorem latticePaths_6_4 : latticePaths 6 4 = 6  := by native_decide
theorem latticePaths_6_6 : latticePaths 6 6 = 1  := by native_decide

/-- For even n, the central count L(n, 0) equals C(n, n/2). -/
example : latticePaths 8 0 = Nat.choose 8 4 := by native_decide

/-! ## 6. Monotone growth of scaled Catalan ratios

  The asymptotic estimate `C_n ~ 4^n / (√π · n^{3/2})` predicts that the
  sequence `n^{3/2} · C_n / 4^n` converges from above.  An integer certificate is:
  the sequence `(2n + 2) * C_n` grows strictly slower than `4 * (2n + 1) * C_{n-1}`
  at each step, which is another face of the recurrence identity.

  We record a selection of strict inequalities between consecutive terms
  of the sequence C_n / 4^n (rescaled to avoid fractions).

  Specifically: the sequence `catalan(n) * n` is strictly increasing relative
  to its 4-fold predecessor `catalan(n-1) * (n-1)` for n ≥ 2.
-/

/-- The ratio C_{n+1}/C_n = (4n+2)/(n+2) is strictly less than 4.
    Equivalently, `catalan(n+1) * (n+2) < 4 * catalan(n) * (n+1)`.
    This is equivalent to the recurrence identity:
    (n+2)*C_{n+1} = (4n+2)*C_n and 4n+2 < 4*(n+1). -/
theorem catalan_scaled_lt_2 : catalan 3 * (3 + 1) < 4 * catalan 2 * (2 + 1) := by native_decide
theorem catalan_scaled_lt_3 : catalan 4 * (4 + 1) < 4 * catalan 3 * (3 + 1) := by native_decide
theorem catalan_scaled_lt_4 : catalan 5 * (5 + 1) < 4 * catalan 4 * (4 + 1) := by native_decide
theorem catalan_scaled_lt_5 : catalan 6 * (6 + 1) < 4 * catalan 5 * (5 + 1) := by native_decide
theorem catalan_scaled_lt_6 : catalan 7 * (7 + 1) < 4 * catalan 6 * (6 + 1) := by native_decide
theorem catalan_scaled_lt_7 : catalan 8 * (8 + 1) < 4 * catalan 7 * (7 + 1) := by native_decide
theorem catalan_scaled_lt_8 : catalan 9 * (9 + 1) < 4 * catalan 8 * (8 + 1) := by native_decide

/-! ## 7. Cross-family consistency: Fuss–Catalan row sums

  For p = 2 with n = 5: the Narayana row sum equals A_2(5).
  For p = 3 with n = 0..5: A_3(n) = ternaryTree(n) (already checked above).
  Here we add a direct tableau for p = 4.
-/

/-- The sequence A_4(0..4) matches the direct C(4n,n)/(3n+1) formula. -/
example : fussCatalan 4 0 = Nat.choose (4 * 0) 0 / (3 * 0 + 1) := by native_decide
example : fussCatalan 4 1 = Nat.choose (4 * 1) 1 / (3 * 1 + 1) := by native_decide
example : fussCatalan 4 2 = Nat.choose (4 * 2) 2 / (3 * 2 + 1) := by native_decide
example : fussCatalan 4 3 = Nat.choose (4 * 3) 3 / (3 * 3 + 1) := by native_decide

/-- Narayana numbers partition Catalan: this is a special case of the
    known identity Σ_{k=1}^{n} N(n,k) = C_n.  We verify up to n = 5. -/
theorem narayana_partition_catalan_3 :
    narayanaSafe 3 1 + narayanaSafe 3 2 + narayanaSafe 3 3 = 5 := by native_decide

theorem narayana_partition_catalan_4 :
    narayanaSafe 4 1 + narayanaSafe 4 2 + narayanaSafe 4 3 + narayanaSafe 4 4 = 14 := by
  native_decide

theorem narayana_partition_catalan_5 :
    narayanaSafe 5 1 + narayanaSafe 5 2 + narayanaSafe 5 3 +
    narayanaSafe 5 4 + narayanaSafe 5 5 = 42 := by native_decide


structure AsymptoticSeriesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AsymptoticSeriesBudgetCertificate.controlled
    (c : AsymptoticSeriesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AsymptoticSeriesBudgetCertificate.budgetControlled
    (c : AsymptoticSeriesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AsymptoticSeriesBudgetCertificate.Ready
    (c : AsymptoticSeriesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AsymptoticSeriesBudgetCertificate.size
    (c : AsymptoticSeriesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem asymptoticSeries_budgetCertificate_le_size
    (c : AsymptoticSeriesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAsymptoticSeriesBudgetCertificate :
    AsymptoticSeriesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAsymptoticSeriesBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticSeriesBudgetCertificate.controlled,
      sampleAsymptoticSeriesBudgetCertificate]
  · norm_num [AsymptoticSeriesBudgetCertificate.budgetControlled,
      sampleAsymptoticSeriesBudgetCertificate]

example :
    sampleAsymptoticSeriesBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticSeriesBudgetCertificate.size := by
  apply asymptoticSeries_budgetCertificate_le_size
  constructor
  · norm_num [AsymptoticSeriesBudgetCertificate.controlled,
      sampleAsymptoticSeriesBudgetCertificate]
  · norm_num [AsymptoticSeriesBudgetCertificate.budgetControlled,
      sampleAsymptoticSeriesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAsymptoticSeriesBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticSeriesBudgetCertificate.controlled,
      sampleAsymptoticSeriesBudgetCertificate]
  · norm_num [AsymptoticSeriesBudgetCertificate.budgetControlled,
      sampleAsymptoticSeriesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAsymptoticSeriesBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticSeriesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AsymptoticSeriesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAsymptoticSeriesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAsymptoticSeriesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.AsymptoticSeries
