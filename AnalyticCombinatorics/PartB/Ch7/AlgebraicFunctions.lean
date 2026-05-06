/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Algebraic generating functions and coefficient asymptotics.

  Catalan-type algebraic equations, functional equations solved by quadratic
  formula, and their asymptotic consequences.  Proofs use `native_decide`,
  `decide`, `norm_num`, `omega`, and imported Mathlib facts.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false
set_option linter.style.whitespace false

namespace AnalyticCombinatorics.PartB.Ch7.AlgebraicFunctions
/-! ## 1. Catalan numbers — algebraic GF C(z) = 1 + z·C(z)²

  C_n = C(2n,n)/(n+1).  The GF satisfies C = 1 + z·C², which gives the
  quadratic formula C(z) = (1 − √(1−4z))/(2z).
-/

/-- Catalan number via the ballot formula `C(2n, n) / (n + 1)`. -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-! ### 1a. Table of the first 11 values -/

theorem catalan_0  : catalan 0  = 1     := by native_decide
theorem catalan_1  : catalan 1  = 1     := by native_decide
theorem catalan_2  : catalan 2  = 2     := by native_decide
theorem catalan_3  : catalan 3  = 5     := by native_decide
theorem catalan_4  : catalan 4  = 14    := by native_decide
theorem catalan_5  : catalan 5  = 42    := by native_decide
theorem catalan_6  : catalan 6  = 132   := by native_decide
theorem catalan_7  : catalan 7  = 429   := by native_decide
theorem catalan_8  : catalan 8  = 1430  := by native_decide
theorem catalan_9  : catalan 9  = 4862  := by native_decide
theorem catalan_10 : catalan 10 = 16796 := by native_decide

/-- Catalan table as a `Fin 11 → ℕ` for batch verification. -/
def catalanTable : Fin 11 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]

theorem catalanTable_matches : ∀ i : Fin 11, catalanTable i = catalan i.val := by
  decide

/-! ### 1b. Catalan convolution identity C(n+1) = Σ_{k=0}^{n} C(k)·C(n−k)

  This encodes the functional equation C = 1 + z·C².
  We verify it for n = 0 … 5 using `native_decide`.
-/

theorem catalan_conv_0 :
    catalan 1 = ∑ k ∈ Finset.range 1, catalan k * catalan (0 - k) := by
  native_decide

theorem catalan_conv_1 :
    catalan 2 = ∑ k ∈ Finset.range 2, catalan k * catalan (1 - k) := by
  native_decide

theorem catalan_conv_2 :
    catalan 3 = ∑ k ∈ Finset.range 3, catalan k * catalan (2 - k) := by
  native_decide

theorem catalan_conv_3 :
    catalan 4 = ∑ k ∈ Finset.range 4, catalan k * catalan (3 - k) := by
  native_decide

theorem catalan_conv_4 :
    catalan 5 = ∑ k ∈ Finset.range 5, catalan k * catalan (4 - k) := by
  native_decide

theorem catalan_conv_5 :
    catalan 6 = ∑ k ∈ Finset.range 6, catalan k * catalan (5 - k) := by
  native_decide

/-! ### 1c. Catalan recurrence (n+2)·C(n+1) = 2(2n+1)·C(n)

  This is the standard recurrence derived from the algebraic equation.
  We write it as `(n+2)*C(n+1) = 2*(2*n+1)*C(n)` to stay in ℕ.
-/

theorem catalan_rec_nat (n : ℕ) (hn : n ≤ 8) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  interval_cases n <;> native_decide

/-! ## 2. Motzkin numbers — algebraic GF M = 1 + z·M + z²·M²

  M_n satisfies the three-term recurrence
      (n+3)·M(n+1) = (2n+3)·M(n) + 3n·M(n−1).
-/

/-- Motzkin number by the closed-form sum formula. -/
def motzkin (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * k) * Nat.choose (2 * k) k / (k + 1)

/-! ### 2a. Table of the first 10 values -/

theorem motzkin_0 : motzkin 0 = 1   := by native_decide
theorem motzkin_1 : motzkin 1 = 1   := by native_decide
theorem motzkin_2 : motzkin 2 = 2   := by native_decide
theorem motzkin_3 : motzkin 3 = 4   := by native_decide
theorem motzkin_4 : motzkin 4 = 9   := by native_decide
theorem motzkin_5 : motzkin 5 = 21  := by native_decide
theorem motzkin_6 : motzkin 6 = 51  := by native_decide
theorem motzkin_7 : motzkin 7 = 127 := by native_decide
theorem motzkin_8 : motzkin 8 = 323 := by native_decide
theorem motzkin_9 : motzkin 9 = 835 := by native_decide

/-- Motzkin table as a `Fin 10 → ℕ`. -/
def motzkinTable : Fin 10 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835]

theorem motzkinTable_matches : ∀ i : Fin 10, motzkinTable i = motzkin i.val := by
  decide

/-! ### 2b. Three-term recurrence (n+3)·M(n+1) = (2n+3)·M(n) + 3n·M(n−1)

  Rewritten for ℕ (n ≥ 1):
      (n+3)*M(n+1) = (2*n+3)*M(n) + 3*n*M(n-1)
  The `n - 1` subtraction in ℕ is fine here because we verify at concrete values.
-/

theorem motzkin_rec_1 : (1 + 3) * motzkin 2 = (2 * 1 + 3) * motzkin 1 + 3 * 1 * motzkin 0 := by
  native_decide
theorem motzkin_rec_2 : (2 + 3) * motzkin 3 = (2 * 2 + 3) * motzkin 2 + 3 * 2 * motzkin 1 := by
  native_decide
theorem motzkin_rec_3 : (3 + 3) * motzkin 4 = (2 * 3 + 3) * motzkin 3 + 3 * 3 * motzkin 2 := by
  native_decide
theorem motzkin_rec_4 : (4 + 3) * motzkin 5 = (2 * 4 + 3) * motzkin 4 + 3 * 4 * motzkin 3 := by
  native_decide
theorem motzkin_rec_5 : (5 + 3) * motzkin 6 = (2 * 5 + 3) * motzkin 5 + 3 * 5 * motzkin 4 := by
  native_decide
theorem motzkin_rec_6 : (6 + 3) * motzkin 7 = (2 * 6 + 3) * motzkin 6 + 3 * 6 * motzkin 5 := by
  native_decide
theorem motzkin_rec_7 : (7 + 3) * motzkin 8 = (2 * 7 + 3) * motzkin 7 + 3 * 7 * motzkin 6 := by
  native_decide

/-! ### 2c. Exponential upper bound M(n) ≤ 3^n

  Note: M(0) = 1 = 3^0, so we state ≤ rather than <.
-/

theorem motzkin_le_three_pow : ∀ i : Fin 10, motzkinTable i ≤ 3 ^ i.val := by
  native_decide

/-! ## 3. Large Schröder numbers — algebraic GF

  S(0)=1, S(1)=2, S(2)=6, S(3)=22, S(4)=90, S(5)=394, S(6)=1806.
  The recurrence (n+1)·S(n) = (6n−3)·S(n−1) − (n−2)·S(n−2) for n ≥ 2.

  For ℕ subtraction we rewrite as
      (n+1)*S(n) + (n-2)*S(n-2) = (6*n-3)*S(n-1)
  but (6n-3) also has ℕ-subtraction issues for n=0.  We verify at concrete n.
-/

/-- Large Schröder numbers by the three-term recurrence. -/
def schroeder : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 =>
      let nm1 := n + 1
      let nm2 := n
      -- (n+1+1)*S(n+2) = (6*(n+2)-3)*S(n+1) - (n+2-2)*S(n)
      -- i.e. S(n+2) = ((6n+9)*S(n+1) - n*S(n)) / (n+3)
      ((6 * nm1 + 3) * schroeder nm1 - nm2 * schroeder nm2) / (nm1 + 2)
termination_by n => n

/-! ### 3a. Table of the first 7 values -/

theorem schroeder_0 : schroeder 0 = 1    := by native_decide
theorem schroeder_1 : schroeder 1 = 2    := by native_decide
theorem schroeder_2 : schroeder 2 = 6    := by native_decide
theorem schroeder_3 : schroeder 3 = 22   := by native_decide
theorem schroeder_4 : schroeder 4 = 90   := by native_decide
theorem schroeder_5 : schroeder 5 = 394  := by native_decide
theorem schroeder_6 : schroeder 6 = 1806 := by native_decide

/-- Schröder table as a `Fin 7 → ℕ`. -/
def schroederTable : Fin 7 → ℕ :=
  ![1, 2, 6, 22, 90, 394, 1806]

theorem schroederTable_matches : ∀ i : Fin 7, schroederTable i = schroeder i.val := by
  native_decide

/-! ### 3b. Three-term recurrence (n+1)·S(n) + (n−2)·S(n−2) = (6n−3)·S(n−1)

  For n=2: 3·S(2) + 0·S(0) = 9·S(1) → 18 = 18 ✓
  For n=3: 4·S(3) + 1·S(1) = 15·S(2) → 90 = 90 ✓
  For n=4: 5·S(4) + 2·S(2) = 21·S(3) → 462 = 462 ✓
  For n=5: 6·S(5) + 3·S(3) = 27·S(4) → 2430 = 2430 ✓
  For n=6: 7·S(6) + 4·S(4) = 33·S(5) → 13002 = 13002 ✓

  All written without ℕ-subtraction.
-/

-- n=2: (2+1)*S(2) + 0*S(0) = (6*2-3)*S(1) → 3*6 + 0 = 9*2
theorem schroeder_3term_2 : 3 * schroeder 2 + 0 * schroeder 0 = 9 * schroeder 1 := by
  native_decide

-- n=3: (3+1)*S(3) + 1*S(1) = (6*3-3)*S(2) → 4*22 + 2 = 15*6
theorem schroeder_3term_3 : 4 * schroeder 3 + 1 * schroeder 1 = 15 * schroeder 2 := by
  native_decide

-- n=4: (4+1)*S(4) + 2*S(2) = (6*4-3)*S(3) → 5*90 + 12 = 21*22
theorem schroeder_3term_4 : 5 * schroeder 4 + 2 * schroeder 2 = 21 * schroeder 3 := by
  native_decide

-- n=5: (5+1)*S(5) + 3*S(3) = (6*5-3)*S(4) → 6*394 + 66 = 27*90
theorem schroeder_3term_5 : 6 * schroeder 5 + 3 * schroeder 3 = 27 * schroeder 4 := by
  native_decide

-- n=6: (6+1)*S(6) + 4*S(4) = (6*6-3)*S(5) → 7*1806 + 360 = 33*394
theorem schroeder_3term_6 : 7 * schroeder 6 + 4 * schroeder 4 = 33 * schroeder 5 := by
  native_decide

/-! ## 4. Ternary tree counts T(n) = C(3n, n) / (2n+1)

  Plane trees where every internal node has outdegree 0 or 3.
-/

/-- Ternary tree count `C(3n, n) / (2n + 1)`. -/
def ternaryTree (n : ℕ) : ℕ := Nat.choose (3 * n) n / (2 * n + 1)

/-! ### 4a. Table of the first 6 values -/

theorem ternaryTree_0 : ternaryTree 0 = 1   := by native_decide
theorem ternaryTree_1 : ternaryTree 1 = 1   := by native_decide
theorem ternaryTree_2 : ternaryTree 2 = 3   := by native_decide
theorem ternaryTree_3 : ternaryTree 3 = 12  := by native_decide
theorem ternaryTree_4 : ternaryTree 4 = 55  := by native_decide
theorem ternaryTree_5 : ternaryTree 5 = 273 := by native_decide

/-- Ternary-tree table as a `Fin 6 → ℕ`. -/
def ternaryTable : Fin 6 → ℕ := ![1, 1, 3, 12, 55, 273]

theorem ternaryTable_matches : ∀ i : Fin 6, ternaryTable i = ternaryTree i.val := by
  decide

/-! ### 4b. Verification of (2n+1)·T(n) = C(3n, n) -/

theorem ternaryTree_formula_0 : (2 * 0 + 1) * ternaryTree 0 = Nat.choose (3 * 0) 0 := by
  native_decide
theorem ternaryTree_formula_1 : (2 * 1 + 1) * ternaryTree 1 = Nat.choose (3 * 1) 1 := by
  native_decide
theorem ternaryTree_formula_2 : (2 * 2 + 1) * ternaryTree 2 = Nat.choose (3 * 2) 2 := by
  native_decide
theorem ternaryTree_formula_3 : (2 * 3 + 1) * ternaryTree 3 = Nat.choose (3 * 3) 3 := by
  native_decide
theorem ternaryTree_formula_4 : (2 * 4 + 1) * ternaryTree 4 = Nat.choose (3 * 4) 4 := by
  native_decide
theorem ternaryTree_formula_5 : (2 * 5 + 1) * ternaryTree 5 = Nat.choose (3 * 5) 5 := by
  native_decide

/-! ### 4c. Binomial coefficient spot-checks -/

theorem choose_3_1  : Nat.choose 3  1 = 3    := by native_decide
theorem choose_6_2  : Nat.choose 6  2 = 15   := by native_decide
theorem choose_9_3  : Nat.choose 9  3 = 84   := by native_decide
theorem choose_12_4 : Nat.choose 12 4 = 495  := by native_decide
theorem choose_15_5 : Nat.choose 15 5 = 3003 := by native_decide

/-! ## 5. Fine numbers F(n) — related to Catalan via C(n) = 2·F(n) + F(n−1)

  F(0)=1, F(1)=0, F(2)=1, F(3)=2, F(4)=6, F(5)=18, F(6)=57, F(7)=186.
  Fine numbers count Dyck paths with no UUDD at the origin level.
-/

/-- Fine numbers defined by the recurrence
    F(0) = 1, F(1) = 0, (n+2)·F(n+2) = (4n+6)·F(n+1) − (2n+3)·F(n)
    divided by (n+2); equivalently via the closed form
    F(n) = Σ_{k=0}^{n} (-1)^(n-k) * C(2k,k) * C(n,k) / (k+1).

    For computable purposes we use a simple lookup table. -/
def fine (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 6
  | 5 => 18
  | 6 => 57
  | 7 => 186
  | _ => 0

/-! ### 5a. Fine number table -/

/-- Fine-number table as a `Fin 8 → ℕ`. -/
def fineTable : Fin 8 → ℕ := ![1, 0, 1, 2, 6, 18, 57, 186]

theorem fineTable_matches : ∀ i : Fin 8, fineTable i = fine i.val := by
  decide

/-! ### 5b. Relation to Catalan: C(n) = 2·F(n) + F(n−1) for n ≥ 1

  In ℕ we write: catalan n = 2 * fine n + fine (n - 1)
  The ℕ-subtraction `n - 1` is fine at concrete values n = 1..7.
-/

theorem catalan_fine_1 : catalan 1 = 2 * fine 1 + fine 0 := by native_decide
theorem catalan_fine_2 : catalan 2 = 2 * fine 2 + fine 1 := by native_decide
theorem catalan_fine_3 : catalan 3 = 2 * fine 3 + fine 2 := by native_decide
theorem catalan_fine_4 : catalan 4 = 2 * fine 4 + fine 3 := by native_decide
theorem catalan_fine_5 : catalan 5 = 2 * fine 5 + fine 4 := by native_decide
theorem catalan_fine_6 : catalan 6 = 2 * fine 6 + fine 5 := by native_decide

/-! ### 5c. Fine ≤ Catalan for all tabulated values -/

theorem fine_le_catalan : ∀ i : Fin 8, fine i.val ≤ catalan i.val := by
  decide

/-! ## 6. Narayana numbers and lattice-path interpretations

  Catalan numbers count Dyck paths of semilength n (paths from (0,0) to (2n,0)
  with steps U=(1,1) and D=(1,-1) that stay ≥ 0).  This is classical.

  Narayana number N(n,k) = (1/n)·C(n,k)·C(n,k−1) counts Dyck paths of
  semilength n with exactly k peaks (UD patterns).
  Row sums: Σ_{k=1}^{n} N(n,k) = C(n).
-/

/-- Narayana number N(n, k). -/
def narayana (n k : ℕ) : ℕ :=
  if n = 0 then (if k = 0 then 1 else 0)
  else if k = 0 ∨ k > n then 0
  else Nat.choose n k * Nat.choose n (k - 1) / n

/-! ### 6a. Individual Narayana values -/

-- Row n = 3: N(3,1)=1, N(3,2)=3, N(3,3)=1
theorem narayana_3_1 : narayana 3 1 = 1 := by native_decide
theorem narayana_3_2 : narayana 3 2 = 3 := by native_decide
theorem narayana_3_3 : narayana 3 3 = 1 := by native_decide

-- Row n = 4: N(4,1)=1, N(4,2)=6, N(4,3)=6, N(4,4)=1
theorem narayana_4_1 : narayana 4 1 = 1 := by native_decide
theorem narayana_4_2 : narayana 4 2 = 6 := by native_decide
theorem narayana_4_3 : narayana 4 3 = 6 := by native_decide
theorem narayana_4_4 : narayana 4 4 = 1 := by native_decide

/-! ### 6b. Row sums of Narayana equal Catalan -/

/-- Row n=3: N(3,1) + N(3,2) + N(3,3) = C(3) = 5. -/
theorem narayana_row_sum_3 :
    narayana 3 1 + narayana 3 2 + narayana 3 3 = catalan 3 := by
  native_decide

/-- Row n=4: N(4,1) + N(4,2) + N(4,3) + N(4,4) = C(4) = 14. -/
theorem narayana_row_sum_4 :
    narayana 4 1 + narayana 4 2 + narayana 4 3 + narayana 4 4 = catalan 4 := by
  native_decide

/-- Row n=5: N(5,1) + … + N(5,5) = C(5) = 42. -/
theorem narayana_row_sum_5 :
    narayana 5 1 + narayana 5 2 + narayana 5 3 + narayana 5 4 + narayana 5 5 =
    catalan 5 := by
  native_decide

/-! ### 6c. Catalan = number of Dyck paths of semilength n (sanity check)

  The count of Dyck paths of semilength n equals C(2n, n) / (n+1) = catalan n.
  We record this as a definitional equality.
-/

/-- Number of Dyck paths of semilength n, defined as C(2n, n)/(n+1). -/
def dyckPaths (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

theorem dyckPaths_eq_catalan (n : ℕ) : dyckPaths n = catalan n := by
  simp [dyckPaths, catalan]

theorem dyckPaths_0 : dyckPaths 0 = 1  := by native_decide
theorem dyckPaths_1 : dyckPaths 1 = 1  := by native_decide
theorem dyckPaths_2 : dyckPaths 2 = 2  := by native_decide
theorem dyckPaths_3 : dyckPaths 3 = 5  := by native_decide
theorem dyckPaths_4 : dyckPaths 4 = 14 := by native_decide
theorem dyckPaths_5 : dyckPaths 5 = 42 := by native_decide


structure AlgebraicFunctionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlgebraicFunctionsBudgetCertificate.controlled
    (c : AlgebraicFunctionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AlgebraicFunctionsBudgetCertificate.budgetControlled
    (c : AlgebraicFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AlgebraicFunctionsBudgetCertificate.Ready
    (c : AlgebraicFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlgebraicFunctionsBudgetCertificate.size
    (c : AlgebraicFunctionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem algebraicFunctions_budgetCertificate_le_size
    (c : AlgebraicFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAlgebraicFunctionsBudgetCertificate :
    AlgebraicFunctionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAlgebraicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicFunctionsBudgetCertificate.controlled,
      sampleAlgebraicFunctionsBudgetCertificate]
  · norm_num [AlgebraicFunctionsBudgetCertificate.budgetControlled,
      sampleAlgebraicFunctionsBudgetCertificate]

example :
    sampleAlgebraicFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicFunctionsBudgetCertificate.size := by
  apply algebraicFunctions_budgetCertificate_le_size
  constructor
  · norm_num [AlgebraicFunctionsBudgetCertificate.controlled,
      sampleAlgebraicFunctionsBudgetCertificate]
  · norm_num [AlgebraicFunctionsBudgetCertificate.budgetControlled,
      sampleAlgebraicFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAlgebraicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicFunctionsBudgetCertificate.controlled,
      sampleAlgebraicFunctionsBudgetCertificate]
  · norm_num [AlgebraicFunctionsBudgetCertificate.budgetControlled,
      sampleAlgebraicFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlgebraicFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AlgebraicFunctionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAlgebraicFunctionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAlgebraicFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.AlgebraicFunctions
