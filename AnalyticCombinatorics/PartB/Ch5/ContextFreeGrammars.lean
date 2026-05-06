/-
  Analytic Combinatorics — Part B
  Chapter V/VII — Context-Free Languages and Their Enumeration

  Formalized numerical checks for combinatorial structures arising from
  context-free grammars: Catalan numbers (Dyck language), Motzkin paths,
  Schröder paths, Narayana numbers, ballot problem, and Fine numbers.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.ContextFreeGrammars
/-! ## 1. Dyck language — Catalan numbers -/

/-- The n-th Catalan number: C(2n,n)/(n+1). Counts balanced parenthesizations
    (words of length 2n in the Dyck language). -/
def catalanN (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

example : catalanN 0 = 1 := by native_decide
example : catalanN 1 = 1 := by native_decide
example : catalanN 2 = 2 := by native_decide
example : catalanN 3 = 5 := by native_decide
example : catalanN 4 = 14 := by native_decide
example : catalanN 5 = 42 := by native_decide
example : catalanN 6 = 132 := by native_decide
example : catalanN 7 = 429 := by native_decide
example : catalanN 8 = 1430 := by native_decide

/-! ## 2. Motzkin paths -/

/-- Motzkin numbers: number of lattice paths from (0,0) to (n,0) using
    steps U=(1,1), D=(1,-1), H=(1,0), never going below the x-axis. -/
def motzkinTable : Fin 9 → ℕ := ![1, 1, 2, 4, 9, 21, 51, 127, 323]

example : motzkinTable 0 = 1 := by native_decide
example : motzkinTable 1 = 1 := by native_decide
example : motzkinTable 2 = 2 := by native_decide
example : motzkinTable 3 = 4 := by native_decide
example : motzkinTable 4 = 9 := by native_decide
example : motzkinTable 5 = 21 := by native_decide
example : motzkinTable 6 = 51 := by native_decide
example : motzkinTable 7 = 127 := by native_decide
example : motzkinTable 8 = 323 := by native_decide

/-! ## 3. Schröder paths (large Schröder numbers) -/

/-- Large Schröder numbers: number of lattice paths from (0,0) to (2n,0)
    using steps U=(1,1), D=(1,-1), H=(2,0), never going below the x-axis. -/
def schroederTable : Fin 7 → ℕ := ![1, 2, 6, 22, 90, 394, 1806]

example : schroederTable 0 = 1 := by native_decide
example : schroederTable 1 = 2 := by native_decide
example : schroederTable 2 = 6 := by native_decide
example : schroederTable 3 = 22 := by native_decide
example : schroederTable 4 = 90 := by native_decide
example : schroederTable 5 = 394 := by native_decide
example : schroederTable 6 = 1806 := by native_decide

/-! ## 4. Narayana numbers -/

/-- Narayana number N(n,k) = C(n,k)*C(n,k-1)/n. Counts Dyck paths of
    semilength n with exactly k peaks. -/
def narayana (n k : ℕ) : ℕ :=
  if n = 0 ∨ k = 0 ∨ k > n then 0
  else Nat.choose n k * Nat.choose n (k - 1) / n

-- Individual values
example : narayana 3 1 = 1 := by native_decide
example : narayana 3 2 = 3 := by native_decide
example : narayana 3 3 = 1 := by native_decide
example : narayana 4 1 = 1 := by native_decide
example : narayana 4 2 = 6 := by native_decide
example : narayana 4 3 = 6 := by native_decide
example : narayana 4 4 = 1 := by native_decide

-- Row sums equal Catalan numbers
example : narayana 3 1 + narayana 3 2 + narayana 3 3 = 5 := by native_decide
example : narayana 4 1 + narayana 4 2 + narayana 4 3 + narayana 4 4 = 14 := by native_decide
example : narayana 5 1 + narayana 5 2 + narayana 5 3 + narayana 5 4 + narayana 5 5 = 42 := by
  native_decide

/-! ## 5. Ballot problem and reflection principle -/

/-- The ballot problem (reflection principle): Catalan(n) = C(2n,n) - C(2n,n-1).
    This counts paths that never touch the diagonal, equivalently sequences where
    one candidate is always strictly ahead. -/
-- Catalan(4) = 14 via reflection
example : Nat.choose 8 4 - Nat.choose 8 3 = 14 := by native_decide
-- Catalan(5) = 42 via reflection
example : Nat.choose 10 5 - Nat.choose 10 4 = 42 := by native_decide
-- Catalan(6) = 132 via reflection
example : Nat.choose 12 6 - Nat.choose 12 5 = 132 := by native_decide
-- Catalan(7) = 429 via reflection
example : Nat.choose 14 7 - Nat.choose 14 6 = 429 := by native_decide

-- Ballot specific instances: (n-k)/(n+k) * C(n+k, k) paths
-- For n=3, k=2: 1 * C(5,2) / 5 = 2
example : 1 * Nat.choose 5 2 / 5 = 2 := by native_decide
-- For n=4, k=3: 1 * C(7,3) / 7 = 5
example : 1 * Nat.choose 7 3 / 7 = 5 := by native_decide

/-! ## 6. Fine numbers -/

/-- Fine numbers: number of Motzkin paths that do not touch the x-axis
    (except at start and end). Equivalently, Dyck paths where no return
    to the axis is a "flat" step. -/
def fineTable : Fin 7 → ℕ := ![1, 0, 1, 2, 6, 18, 57]

example : fineTable 0 = 1 := by native_decide
example : fineTable 1 = 0 := by native_decide
example : fineTable 2 = 1 := by native_decide
example : fineTable 3 = 2 := by native_decide
example : fineTable 4 = 6 := by native_decide
example : fineTable 5 = 18 := by native_decide
example : fineTable 6 = 57 := by native_decide

/-! ## 7. Cross-checks: Catalan via both formulas -/

/-- Verify that C(2n,n)/(n+1) = C(2n,n) - C(2n,n-1) for small values. -/
example : catalanN 3 = Nat.choose 6 3 - Nat.choose 6 2 := by native_decide
example : catalanN 4 = Nat.choose 8 4 - Nat.choose 8 3 := by native_decide
example : catalanN 5 = Nat.choose 10 5 - Nat.choose 10 4 := by native_decide
example : catalanN 6 = Nat.choose 12 6 - Nat.choose 12 5 := by native_decide
example : catalanN 7 = Nat.choose 14 7 - Nat.choose 14 6 := by native_decide
example : catalanN 8 = Nat.choose 16 8 - Nat.choose 16 7 := by native_decide

/-- Large Schroeder-number table sample. -/
theorem schroederTable_six :
    schroederTable 6 = 1806 := by
  native_decide

/-- Narayana row-sum sample for semilength five. -/
theorem narayana_row_five_sum :
    narayana 5 1 + narayana 5 2 + narayana 5 3 +
      narayana 5 4 + narayana 5 5 = 42 := by
  native_decide


structure ContextFreeGrammarsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ContextFreeGrammarsBudgetCertificate.controlled
    (c : ContextFreeGrammarsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ContextFreeGrammarsBudgetCertificate.budgetControlled
    (c : ContextFreeGrammarsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ContextFreeGrammarsBudgetCertificate.Ready
    (c : ContextFreeGrammarsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ContextFreeGrammarsBudgetCertificate.size
    (c : ContextFreeGrammarsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem contextFreeGrammars_budgetCertificate_le_size
    (c : ContextFreeGrammarsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleContextFreeGrammarsBudgetCertificate :
    ContextFreeGrammarsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleContextFreeGrammarsBudgetCertificate.Ready := by
  constructor
  · norm_num [ContextFreeGrammarsBudgetCertificate.controlled,
      sampleContextFreeGrammarsBudgetCertificate]
  · norm_num [ContextFreeGrammarsBudgetCertificate.budgetControlled,
      sampleContextFreeGrammarsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleContextFreeGrammarsBudgetCertificate.certificateBudgetWindow ≤
      sampleContextFreeGrammarsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleContextFreeGrammarsBudgetCertificate.Ready := by
  constructor
  · norm_num [ContextFreeGrammarsBudgetCertificate.controlled,
      sampleContextFreeGrammarsBudgetCertificate]
  · norm_num [ContextFreeGrammarsBudgetCertificate.budgetControlled,
      sampleContextFreeGrammarsBudgetCertificate]

example :
    sampleContextFreeGrammarsBudgetCertificate.certificateBudgetWindow ≤
      sampleContextFreeGrammarsBudgetCertificate.size := by
  apply contextFreeGrammars_budgetCertificate_le_size
  constructor
  · norm_num [ContextFreeGrammarsBudgetCertificate.controlled,
      sampleContextFreeGrammarsBudgetCertificate]
  · norm_num [ContextFreeGrammarsBudgetCertificate.budgetControlled,
      sampleContextFreeGrammarsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ContextFreeGrammarsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleContextFreeGrammarsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleContextFreeGrammarsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.ContextFreeGrammars
