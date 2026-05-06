/-
  Analytic Combinatorics — Part B
  Chapter V — Automata and Languages

  Numerical verifications related to the transfer matrix method and
  finite-automaton enumeration (Flajolet & Sedgewick, Ch V).

  Topics covered:
  1. Binary strings with no consecutive 1s  (Fibonacci / transfer-matrix)
  2. Binary strings avoiding "000"           (tribonacci-like recurrence)
  3. Ternary strings avoiding "aa"           (2-state DFA recurrence)
  4. Run-length encoding counts              (C(n-1,k-1) formula)
  5. de Bruijn sequence counts               (BEST theorem for k=2)
  6. Binary necklaces                        (Burnside / table)
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.FiniteAutomata
/-! ## 1. Binary strings with no consecutive 1s

  DFA: two states S0 (start / last symbol was 0) and S1 (last symbol was 1).
  Transitions: S0 →0→ S0, S0 →1→ S1, S1 →0→ S0, S1 →1→ (reject / dead).

  The count of accepted strings of length n equals Fibonacci(n+2). -/

/-- Number of binary strings of length n containing no two consecutive 1s.
    Equals `Nat.fib (n + 2)`. -/
def noConsec (n : ℕ) : ℕ := Nat.fib (n + 2)

example : noConsec 0 = 1 := by native_decide
example : noConsec 1 = 2 := by native_decide
example : noConsec 2 = 3 := by native_decide
example : noConsec 3 = 5 := by native_decide
example : noConsec 4 = 8 := by native_decide
example : noConsec 5 = 13 := by native_decide
example : noConsec 6 = 21 := by native_decide

-- Every accepted string is a binary string, so noConsec n ≤ 2^n.
example : noConsec 0 ≤ 2 ^ 0 := by native_decide
example : noConsec 1 ≤ 2 ^ 1 := by native_decide
example : noConsec 2 ≤ 2 ^ 2 := by native_decide
example : noConsec 3 ≤ 2 ^ 3 := by native_decide
example : noConsec 4 ≤ 2 ^ 4 := by native_decide
example : noConsec 5 ≤ 2 ^ 5 := by native_decide
example : noConsec 6 ≤ 2 ^ 6 := by native_decide
example : noConsec 7 ≤ 2 ^ 7 := by native_decide
example : noConsec 8 ≤ 2 ^ 8 := by native_decide

/-! ## 2. Binary strings avoiding "000"

  Transfer matrix for the DFA tracking the length of the current run of 0s:
  states {ε, 0, 00}, plus a dead (reject) state for "000".

  The resulting recurrence is:
    T(n) = T(n-1) + T(n-2) + T(n-3),   n ≥ 3
    T(0) = 1, T(1) = 2, T(2) = 4.

  (Tribonacci-like; every length-n string is built by appending 1 — keeping
  the last run short — or reading 0/00 followed by 1, reducing to a shorter
  string.) -/

/-- Number of binary strings of length n with no run of three consecutive 0s. -/
def noTriple : ℕ → ℕ
  | 0     => 1
  | 1     => 2
  | 2     => 4
  | n + 3 => noTriple (n + 2) + noTriple (n + 1) + noTriple n

example : noTriple 0 = 1  := by native_decide
example : noTriple 1 = 2  := by native_decide
example : noTriple 2 = 4  := by native_decide
example : noTriple 3 = 7  := by native_decide
example : noTriple 4 = 13 := by native_decide
example : noTriple 5 = 24 := by native_decide
example : noTriple 6 = 44 := by native_decide
example : noTriple 7 = 81 := by native_decide

-- noTriple n ≤ 2^n for small n.
example : noTriple 0 ≤ 2 ^ 0 := by native_decide
example : noTriple 1 ≤ 2 ^ 1 := by native_decide
example : noTriple 2 ≤ 2 ^ 2 := by native_decide
example : noTriple 3 ≤ 2 ^ 3 := by native_decide
example : noTriple 4 ≤ 2 ^ 4 := by native_decide
example : noTriple 5 ≤ 2 ^ 5 := by native_decide
example : noTriple 6 ≤ 2 ^ 6 := by native_decide
example : noTriple 7 ≤ 2 ^ 7 := by native_decide
example : noTriple 8 ≤ 2 ^ 8 := by native_decide

/-! ## 3. Ternary strings over {a, b, c} avoiding the pattern "aa"

  DFA: two states — "neutral" (last symbol ≠ a, or start) and "saw-a"
  (last symbol = a).  From neutral we may append a, b, or c (3 choices);
  from saw-a we may append b or c only (2 choices; appending a leads to
  the forbidden pattern).

  Let f(n) = total strings of length n over {a,b,c} avoiding "aa".
  Enumerating by the last letter:
    f(n) = (strings ending in b or c) + (strings ending in a)
         = 2 · f(n-1) + 2 · f(n-2),   n ≥ 2
    f(0) = 1,  f(1) = 3.

  (The 2·f(n-2) term counts strings whose second-to-last letter is NOT a,
  followed by "a"; the 2·f(n-1) term counts strings appended with b or c.) -/

/-- Number of length-n strings over {a, b, c} containing no "aa". -/
def avoid_aa : ℕ → ℕ
  | 0     => 1
  | 1     => 3
  | n + 2 => 2 * avoid_aa (n + 1) + 2 * avoid_aa n

example : avoid_aa 0 = 1  := by native_decide
example : avoid_aa 1 = 3  := by native_decide
example : avoid_aa 2 = 8  := by native_decide
example : avoid_aa 3 = 22 := by native_decide
example : avoid_aa 4 = 60 := by native_decide
example : avoid_aa 5 = 164 := by native_decide
example : avoid_aa 6 = 448 := by native_decide

-- Sanity: exactly one length-2 string over {a,b,c} is forbidden ("aa"),
-- so avoid_aa 2 = 3^2 - 1 = 8.
example : avoid_aa 2 = 3 ^ 2 - 1 := by native_decide

-- avoid_aa n ≤ 3^n for small n.
example : avoid_aa 0 ≤ 3 ^ 0 := by native_decide
example : avoid_aa 1 ≤ 3 ^ 1 := by native_decide
example : avoid_aa 2 ≤ 3 ^ 2 := by native_decide
example : avoid_aa 3 ≤ 3 ^ 3 := by native_decide
example : avoid_aa 4 ≤ 3 ^ 4 := by native_decide
example : avoid_aa 5 ≤ 3 ^ 5 := by native_decide
example : avoid_aa 6 ≤ 3 ^ 6 := by native_decide

/-! ## 4. Run-length encoding

  A *run* is a maximal block of identical symbols.  Every binary string of
  length n ≥ 1 with exactly k runs (k ≥ 1) is determined by:
  • a choice of first symbol (2 options), and
  • a composition of n into k positive parts (one part per run): C(n-1, k-1).
  Hence the count is 2 · C(n-1, k-1).

  Special case k = 0: only the empty string (n = 0) has zero runs. -/

/-- Number of binary strings of length n with exactly k runs. -/
def stringsByRuns (n k : ℕ) : ℕ :=
  if k = 0 then (if n = 0 then 1 else 0)
  else 2 * Nat.choose (n - 1) (k - 1)

-- Spot-checks for n = 4:
-- k=1: "0000","1111"                                → 2
-- k=2: e.g. "0001","0011","0111","1000","1100","1110" → 6
-- k=3: e.g. "0010","0100","0110","1001","1011","1101" → 6
-- k=4: "0101","1010"                                  → 2
example : stringsByRuns 4 1 = 2 := by native_decide
example : stringsByRuns 4 2 = 6 := by native_decide
example : stringsByRuns 4 3 = 6 := by native_decide
example : stringsByRuns 4 4 = 2 := by native_decide
example : stringsByRuns 4 0 = 0 := by native_decide

-- Total over all k equals 2^n.
example : (Finset.range 5).sum (stringsByRuns 4) = 2 ^ 4 := by native_decide
example : (Finset.range 6).sum (stringsByRuns 5) = 2 ^ 5 := by native_decide
example : (Finset.range 7).sum (stringsByRuns 6) = 2 ^ 6 := by native_decide

-- k cannot exceed n (pigeonhole: each run has length ≥ 1).
example : stringsByRuns 4 5 = 0 := by native_decide
example : stringsByRuns 3 4 = 0 := by native_decide

/-! ## 5. de Bruijn sequences (k = 2)

  A de Bruijn sequence of order n over a binary alphabet is a cyclic string
  of length 2^n in which every binary string of length n appears exactly once
  as a (cyclic) substring.

  By the BEST (de Bruijn–Ehrenfest–Smith–Tutte) theorem, the number of
  distinct such sequences is

      B(2, n) = (2!)^{2^{n-1}} / 2^n  =  2^{2^{n-1}} / 2^n.

  Values: B(2,1)=1, B(2,2)=1, B(2,3)=2, B(2,4)=16. -/

/-- Number of de Bruijn sequences of order n over a binary alphabet,
    via the BEST theorem: `2^{2^{n-1}} / 2^n`. -/
def deBruijnCount (n : ℕ) : ℕ :=
  2 ^ (2 ^ (n - 1)) / 2 ^ n

example : deBruijnCount 1 = 1  := by native_decide
example : deBruijnCount 2 = 1  := by native_decide
example : deBruijnCount 3 = 2  := by native_decide
example : deBruijnCount 4 = 16 := by native_decide

-- The sequence length is 2^n; verify for small n.
-- (Each de Bruijn sequence covers all 2^n length-n substrings exactly once.)
example : (2 : ℕ) ^ 1 = 2  := by native_decide
example : (2 : ℕ) ^ 2 = 4  := by native_decide
example : (2 : ℕ) ^ 3 = 8  := by native_decide
example : (2 : ℕ) ^ 4 = 16 := by native_decide

/-! ## 6. Binary necklaces (Burnside / Pólya)

  A binary necklace of length n is an equivalence class of binary strings
  under cyclic rotation.  By Burnside's lemma,

      N(n) = (1/n) · Σ_{d | n} φ(n/d) · 2^d       (n ≥ 1),
      N(0) = 1  (by convention).

  The sequence begins: N(1)=2, N(2)=3, N(3)=4, N(4)=6, N(5)=8,
  N(6)=14, N(7)=20, N(8)=36. -/

/-- Lookup table for N(n), n = 0..8 (index = n). -/
def necklaceTable : Fin 9 → ℕ := ![1, 2, 3, 4, 6, 8, 14, 20, 36]

-- The table agrees with the Burnside formula for prime lengths:
-- For prime p, N(p) = (2^p - 2) / p + 2.
example : necklaceTable ⟨5, by norm_num⟩ = (2 ^ 5 - 2) / 5 + 2 := by native_decide
example : necklaceTable ⟨7, by norm_num⟩ = (2 ^ 7 - 2) / 7 + 2 := by native_decide

-- For n = 4 (non-prime), verify directly via the Burnside sum:
-- Σ_{d | 4} φ(4/d) · 2^d = φ(4)·2 + φ(2)·4 + φ(1)·16 = 4+4+16 = 24; 24/4 = 6.
example : (Nat.totient 4 * 2 ^ 1 + Nat.totient 2 * 2 ^ 2 + Nat.totient 1 * 2 ^ 4) / 4
    = necklaceTable ⟨4, by norm_num⟩ := by native_decide

-- For n = 6: Σ_{d | 6} φ(6/d)·2^d / 6
-- divisors of 6: 1,2,3,6
-- φ(6)·2 + φ(3)·4 + φ(2)·8 + φ(1)·64 = 2·2+2·4+1·8+1·64 = 4+8+8+64 = 84; 84/6=14.
example : (Nat.totient 6 * 2 ^ 1 + Nat.totient 3 * 2 ^ 2 +
           Nat.totient 2 * 2 ^ 3 + Nat.totient 1 * 2 ^ 6) / 6
    = necklaceTable ⟨6, by norm_num⟩ := by native_decide

-- n · N(n) ≥ 2^n (each necklace has at most n distinct rotations, so
-- the orbit-counting inequality gives n · N(n) ≥ 2^n, with equality iff
-- all strings are aperiodic — true for prime n).
example : 1 * necklaceTable ⟨1, by norm_num⟩ ≥ 2 ^ 1 := by native_decide
example : 2 * necklaceTable ⟨2, by norm_num⟩ ≥ 2 ^ 2 := by native_decide
example : 3 * necklaceTable ⟨3, by norm_num⟩ ≥ 2 ^ 3 := by native_decide
example : 4 * necklaceTable ⟨4, by norm_num⟩ ≥ 2 ^ 4 := by native_decide
example : 5 * necklaceTable ⟨5, by norm_num⟩ ≥ 2 ^ 5 := by native_decide
example : 6 * necklaceTable ⟨6, by norm_num⟩ ≥ 2 ^ 6 := by native_decide
example : 7 * necklaceTable ⟨7, by norm_num⟩ ≥ 2 ^ 7 := by native_decide
example : 8 * necklaceTable ⟨8, by norm_num⟩ ≥ 2 ^ 8 := by native_decide

-- For prime n, the count is exact: n · N(n) = 2^n - 2 + 2n (two fixed-point
-- necklaces: all-0 and all-1, each with orbit size 1, contributing 2 to
-- the Burnside sum regardless of prime-ness).
-- Equivalently, 5 · N(5) = 2^5 + 5·2 - 2·5 ... let's just verify the prime formula.
example : necklaceTable ⟨5, by norm_num⟩ = (2 ^ 5 - 2) / 5 + 2 := by native_decide
example : necklaceTable ⟨7, by norm_num⟩ = (2 ^ 7 - 2) / 7 + 2 := by native_decide

/-- Binary de Bruijn count sample at order four. -/
theorem deBruijnCount_four :
    deBruijnCount 4 = 16 := by
  native_decide

/-- Binary necklace prime-length sample. -/
theorem necklaceTable_seven_prime_formula :
    necklaceTable ⟨7, by norm_num⟩ = (2 ^ 7 - 2) / 7 + 2 := by
  native_decide


structure FiniteAutomataBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteAutomataBudgetCertificate.controlled
    (c : FiniteAutomataBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteAutomataBudgetCertificate.budgetControlled
    (c : FiniteAutomataBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteAutomataBudgetCertificate.Ready
    (c : FiniteAutomataBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteAutomataBudgetCertificate.size
    (c : FiniteAutomataBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteAutomata_budgetCertificate_le_size
    (c : FiniteAutomataBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteAutomataBudgetCertificate :
    FiniteAutomataBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteAutomataBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteAutomataBudgetCertificate.controlled,
      sampleFiniteAutomataBudgetCertificate]
  · norm_num [FiniteAutomataBudgetCertificate.budgetControlled,
      sampleFiniteAutomataBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteAutomataBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteAutomataBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteAutomataBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteAutomataBudgetCertificate.controlled,
      sampleFiniteAutomataBudgetCertificate]
  · norm_num [FiniteAutomataBudgetCertificate.budgetControlled,
      sampleFiniteAutomataBudgetCertificate]

example :
    sampleFiniteAutomataBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteAutomataBudgetCertificate.size := by
  apply finiteAutomata_budgetCertificate_le_size
  constructor
  · norm_num [FiniteAutomataBudgetCertificate.controlled,
      sampleFiniteAutomataBudgetCertificate]
  · norm_num [FiniteAutomataBudgetCertificate.budgetControlled,
      sampleFiniteAutomataBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteAutomataBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteAutomataBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteAutomataBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.FiniteAutomata
