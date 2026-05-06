/-
  Chapter I appendix / Chapter II — unlabelled structures.

  The main concrete example here is the Burnside/Pólya count for binary
  necklaces, i.e. cyclic equivalence classes of binary words of length `n`.
-/
import Mathlib.Tactic

set_option linter.style.show false
set_option linter.style.nativeDecide false

open Finset

namespace AnalyticCombinatorics.PartA.Ch1.UnlabelledStructures
/-- The Burnside numerator for binary necklaces of length `n`.

For `n > 0`, Burnside's lemma for the cyclic group gives

`necklaceCountTimesN n = ∑_{d | n} φ(d) * 2 ^ (n / d)`,

so the actual count is this quantity divided by `n`.
-/
def necklaceCountTimesN (n : ℕ) : ℕ :=
  ∑ d ∈ Nat.divisors n, Nat.totient d * 2 ^ (n / d)

/-- Number of binary necklaces of length `n`.

The `n = 0` value records the unique empty necklace. For positive `n`, this is
the standard Pólya/Burnside formula

`(1 / n) * ∑_{d | n} φ(d) * 2 ^ (n / d)`,

written with exact natural-number division.
-/
def necklaceCount (n : ℕ) : ℕ :=
  if n = 0 then 1 else necklaceCountTimesN n / n

example : necklaceCount 0 = 1 := by native_decide
example : necklaceCount 1 = 2 := by native_decide
example : necklaceCount 2 = 3 := by native_decide
example : necklaceCount 3 = 4 := by native_decide
example : necklaceCount 4 = 6 := by native_decide
example : necklaceCount 5 = 8 := by native_decide
example : necklaceCount 6 = 14 := by native_decide
example : necklaceCount 7 = 20 := by native_decide
example : necklaceCount 8 = 36 := by native_decide

example : necklaceCountTimesN 1 = 1 * necklaceCount 1 := by native_decide
example : necklaceCountTimesN 2 = 2 * necklaceCount 2 := by native_decide
example : necklaceCountTimesN 3 = 3 * necklaceCount 3 := by native_decide
example : necklaceCountTimesN 4 = 4 * necklaceCount 4 := by native_decide
example : necklaceCountTimesN 5 = 5 * necklaceCount 5 := by native_decide
example : necklaceCountTimesN 6 = 6 * necklaceCount 6 := by native_decide
example : necklaceCountTimesN 7 = 7 * necklaceCount 7 := by native_decide
example : necklaceCountTimesN 8 = 8 * necklaceCount 8 := by native_decide

example : 1 ∣ necklaceCountTimesN 1 := by native_decide
example : 2 ∣ necklaceCountTimesN 2 := by native_decide
example : 3 ∣ necklaceCountTimesN 3 := by native_decide
example : 4 ∣ necklaceCountTimesN 4 := by native_decide
example : 5 ∣ necklaceCountTimesN 5 := by native_decide
example : 6 ∣ necklaceCountTimesN 6 := by native_decide
example : 7 ∣ necklaceCountTimesN 7 := by native_decide
example : 8 ∣ necklaceCountTimesN 8 := by native_decide

/-- Initial values of OEIS A000055: non-isomorphic unrooted trees by number of vertices.

The `0` case is set to `0`; the listed sequence starts at `n = 1`.
-/
def unrootedTreeCount : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | 7 => 6
  | 8 => 11
  | 9 => 23
  | _ => 0

example : unrootedTreeCount 1 = 1 := by native_decide
example : unrootedTreeCount 2 = 1 := by native_decide
example : unrootedTreeCount 3 = 1 := by native_decide
example : unrootedTreeCount 4 = 1 := by native_decide
example : unrootedTreeCount 5 = 2 := by native_decide
example : unrootedTreeCount 6 = 3 := by native_decide
example : unrootedTreeCount 7 = 6 := by native_decide
example : unrootedTreeCount 8 = 11 := by native_decide
example : unrootedTreeCount 9 = 23 := by native_decide

/-- Binary necklace count at length eight. -/
theorem necklaceCount_eight :
    necklaceCount 8 = 36 := by
  native_decide

/-- Burnside numerator divisibility sample for length eight. -/
theorem necklaceCountTimesN_eight :
    necklaceCountTimesN 8 = 8 * necklaceCount 8 := by
  native_decide

/-- Unlabelled tree table sample at nine vertices. -/
theorem unrootedTreeCount_nine :
    unrootedTreeCount 9 = 23 := by
  native_decide


structure UnlabelledStructuresBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UnlabelledStructuresBudgetCertificate.controlled
    (c : UnlabelledStructuresBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UnlabelledStructuresBudgetCertificate.budgetControlled
    (c : UnlabelledStructuresBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UnlabelledStructuresBudgetCertificate.Ready
    (c : UnlabelledStructuresBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UnlabelledStructuresBudgetCertificate.size
    (c : UnlabelledStructuresBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem unlabelledStructures_budgetCertificate_le_size
    (c : UnlabelledStructuresBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUnlabelledStructuresBudgetCertificate :
    UnlabelledStructuresBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUnlabelledStructuresBudgetCertificate.Ready := by
  constructor
  · norm_num [UnlabelledStructuresBudgetCertificate.controlled,
      sampleUnlabelledStructuresBudgetCertificate]
  · norm_num [UnlabelledStructuresBudgetCertificate.budgetControlled,
      sampleUnlabelledStructuresBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUnlabelledStructuresBudgetCertificate.certificateBudgetWindow ≤
      sampleUnlabelledStructuresBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUnlabelledStructuresBudgetCertificate.Ready := by
  constructor
  · norm_num [UnlabelledStructuresBudgetCertificate.controlled,
      sampleUnlabelledStructuresBudgetCertificate]
  · norm_num [UnlabelledStructuresBudgetCertificate.budgetControlled,
      sampleUnlabelledStructuresBudgetCertificate]

example :
    sampleUnlabelledStructuresBudgetCertificate.certificateBudgetWindow ≤
      sampleUnlabelledStructuresBudgetCertificate.size := by
  apply unlabelledStructures_budgetCertificate_le_size
  constructor
  · norm_num [UnlabelledStructuresBudgetCertificate.controlled,
      sampleUnlabelledStructuresBudgetCertificate]
  · norm_num [UnlabelledStructuresBudgetCertificate.budgetControlled,
      sampleUnlabelledStructuresBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UnlabelledStructuresBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUnlabelledStructuresBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUnlabelledStructuresBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.UnlabelledStructures
