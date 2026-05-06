import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.OrdinaryGFApplications


/-!
Finite, computable checks for ordinary generating function applications
from Chapter IV of Flajolet--Sedgewick.
-/

open Finset

/-! ## 1. Compositions of `n`

A composition of `n >= 1` is encoded by the subset of the `n - 1`
interior gaps where a separator is placed.
-/

def compositionCount (n : ℕ) : ℕ :=
  (Finset.range (n - 1)).powerset.card

example : compositionCount 1 = 1 := by native_decide
example : compositionCount 2 = 2 := by native_decide
example : compositionCount 3 = 4 := by native_decide
example : compositionCount 4 = 8 := by native_decide
example : compositionCount 5 = 16 := by native_decide
example : compositionCount 6 = 32 := by native_decide
example : compositionCount 7 = 64 := by native_decide
example : compositionCount 8 = 128 := by native_decide

example :
    ∀ n ∈ Finset.Icc 1 12, compositionCount n = 2 ^ (n - 1) := by
  native_decide

/-! ## 2. Lattice paths and ballot numbers -/

def latticePathCount (east north : ℕ) : ℕ :=
  Nat.choose (east + north) east

def weakBallotNumber (p q : ℕ) : ℕ :=
  if q = 0 then 1
  else if q ≤ p then Nat.choose (p + q) q - Nat.choose (p + q) (q - 1)
  else 0

def bertrandBallotNumber (p q : ℕ) : ℕ :=
  if q < p then ((p - q) * Nat.choose (p + q) q) / (p + q)
  else 0

example : latticePathCount 0 0 = 1 := by native_decide
example : latticePathCount 2 3 = 10 := by native_decide
example : latticePathCount 4 4 = 70 := by native_decide
example : latticePathCount 6 2 = 28 := by native_decide

example : weakBallotNumber 0 0 = 1 := by native_decide
example : weakBallotNumber 1 1 = 1 := by native_decide
example : weakBallotNumber 2 1 = 2 := by native_decide
example : weakBallotNumber 2 2 = 2 := by native_decide
example : weakBallotNumber 3 2 = 5 := by native_decide
example : weakBallotNumber 4 2 = 9 := by native_decide
example : weakBallotNumber 4 4 = 14 := by native_decide
example : weakBallotNumber 2 3 = 0 := by native_decide

example : bertrandBallotNumber 1 0 = 1 := by native_decide
example : bertrandBallotNumber 2 1 = 1 := by native_decide
example : bertrandBallotNumber 3 1 = 2 := by native_decide
example : bertrandBallotNumber 3 2 = 2 := by native_decide
example : bertrandBallotNumber 4 2 = 5 := by native_decide
example : bertrandBallotNumber 5 2 = 9 := by native_decide
example : bertrandBallotNumber 5 3 = 14 := by native_decide
example : bertrandBallotNumber 3 3 = 0 := by native_decide

example :
    ∀ p ∈ Finset.range 8, ∀ q ∈ Finset.range 8,
      q < p →
        (p + q) * bertrandBallotNumber p q =
          (p - q) * Nat.choose (p + q) q := by
  native_decide

/-! ## 3. Derangements and the subfactorial formula -/

def derangementNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangementNumber (n + 1) + derangementNumber n)

def subfactorialFormula (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (if k % 2 = 0 then (1 : ℤ) else -1) *
      ((n.factorial / k.factorial : ℕ) : ℤ)

example : derangementNumber 0 = 1 := by native_decide
example : derangementNumber 1 = 0 := by native_decide
example : derangementNumber 2 = 1 := by native_decide
example : derangementNumber 3 = 2 := by native_decide
example : derangementNumber 4 = 9 := by native_decide
example : derangementNumber 5 = 44 := by native_decide
example : derangementNumber 6 = 265 := by native_decide
example : derangementNumber 7 = 1854 := by native_decide
example : derangementNumber 8 = 14833 := by native_decide

example : subfactorialFormula 0 = 1 := by native_decide
example : subfactorialFormula 1 = 0 := by native_decide
example : subfactorialFormula 2 = 1 := by native_decide
example : subfactorialFormula 3 = 2 := by native_decide
example : subfactorialFormula 4 = 9 := by native_decide
example : subfactorialFormula 5 = 44 := by native_decide
example : subfactorialFormula 6 = 265 := by native_decide
example : subfactorialFormula 7 = 1854 := by native_decide
example : subfactorialFormula 8 = 14833 := by native_decide

example :
    ∀ n ∈ Finset.range 9,
      (derangementNumber n : ℤ) = subfactorialFormula n := by
  native_decide

/-! ## 4. Partitions with restricted parts -/

def restrictedPartitionCount : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, n =>
      ∑ m ∈ Finset.range (n / (k + 1) + 1),
        restrictedPartitionCount k (n - m * (k + 1))

example : restrictedPartitionCount 0 0 = 1 := by native_decide
example : restrictedPartitionCount 0 5 = 0 := by native_decide

example : restrictedPartitionCount 1 0 = 1 := by native_decide
example : restrictedPartitionCount 1 1 = 1 := by native_decide
example : restrictedPartitionCount 1 6 = 1 := by native_decide

example : restrictedPartitionCount 2 0 = 1 := by native_decide
example : restrictedPartitionCount 2 1 = 1 := by native_decide
example : restrictedPartitionCount 2 2 = 2 := by native_decide
example : restrictedPartitionCount 2 3 = 2 := by native_decide
example : restrictedPartitionCount 2 4 = 3 := by native_decide
example : restrictedPartitionCount 2 5 = 3 := by native_decide
example : restrictedPartitionCount 2 6 = 4 := by native_decide

example : restrictedPartitionCount 3 3 = 3 := by native_decide
example : restrictedPartitionCount 3 4 = 4 := by native_decide
example : restrictedPartitionCount 3 5 = 5 := by native_decide
example : restrictedPartitionCount 3 6 = 7 := by native_decide
example : restrictedPartitionCount 4 5 = 6 := by native_decide
example : restrictedPartitionCount 4 6 = 9 := by native_decide

example :
    ∀ n ∈ Finset.range 10,
      restrictedPartitionCount 1 n = 1 := by
  native_decide

example :
    ∀ n ∈ Finset.range 10,
      restrictedPartitionCount 2 n = n / 2 + 1 := by
  native_decide

/-! ## 5. Fibonacci tilings -/

def tilingCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => tilingCount (n + 1) + tilingCount n

example : tilingCount 0 = 1 := by native_decide
example : tilingCount 1 = 1 := by native_decide
example : tilingCount 2 = 2 := by native_decide
example : tilingCount 3 = 3 := by native_decide
example : tilingCount 4 = 5 := by native_decide
example : tilingCount 5 = 8 := by native_decide
example : tilingCount 6 = 13 := by native_decide
example : tilingCount 7 = 21 := by native_decide
example : tilingCount 8 = 34 := by native_decide

example :
    ∀ n ∈ Finset.range 12, tilingCount n = Nat.fib (n + 1) := by
  native_decide

/-! ## 6. Catalan numbers from ballot numbers -/

def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

def catalanFromBallot (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1)

example : catalanNumber 0 = 1 := by native_decide
example : catalanNumber 1 = 1 := by native_decide
example : catalanNumber 2 = 2 := by native_decide
example : catalanNumber 3 = 5 := by native_decide
example : catalanNumber 4 = 14 := by native_decide
example : catalanNumber 5 = 42 := by native_decide
example : catalanNumber 6 = 132 := by native_decide
example : catalanNumber 7 = 429 := by native_decide

example : catalanFromBallot 0 = 1 := by native_decide
example : catalanFromBallot 1 = 1 := by native_decide
example : catalanFromBallot 2 = 2 := by native_decide
example : catalanFromBallot 3 = 5 := by native_decide
example : catalanFromBallot 4 = 14 := by native_decide
example : catalanFromBallot 5 = 42 := by native_decide
example : catalanFromBallot 6 = 132 := by native_decide
example : catalanFromBallot 7 = 429 := by native_decide

example :
    ∀ n ∈ Finset.range 10,
      catalanNumber n =
        Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1) := by
  native_decide

example :
    ∀ n ∈ Finset.range 10,
      catalanNumber n = catalanFromBallot n := by
  native_decide

/-- Composition count sample extracted from the OGF model. -/
theorem compositionCount_eight :
    compositionCount 8 = 128 := by
  native_decide

/-- Weak ballot number sample. -/
theorem weakBallotNumber_four_four :
    weakBallotNumber 4 4 = 14 := by
  native_decide

/-- Derangement-number sample for the ordinary generating function checks. -/
theorem derangementNumber_eight :
    derangementNumber 8 = 14833 := by
  native_decide

/-- Catalan ballot extraction sample. -/
theorem catalanFromBallot_seven :
    catalanFromBallot 7 = 429 := by
  native_decide



structure OrdinaryGFApplicationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def OrdinaryGFApplicationsBudgetCertificate.controlled
    (c : OrdinaryGFApplicationsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def OrdinaryGFApplicationsBudgetCertificate.budgetControlled
    (c : OrdinaryGFApplicationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def OrdinaryGFApplicationsBudgetCertificate.Ready
    (c : OrdinaryGFApplicationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def OrdinaryGFApplicationsBudgetCertificate.size
    (c : OrdinaryGFApplicationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem ordinaryGFApplications_budgetCertificate_le_size
    (c : OrdinaryGFApplicationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleOrdinaryGFApplicationsBudgetCertificate :
    OrdinaryGFApplicationsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleOrdinaryGFApplicationsBudgetCertificate.Ready := by
  constructor
  · norm_num [OrdinaryGFApplicationsBudgetCertificate.controlled,
      sampleOrdinaryGFApplicationsBudgetCertificate]
  · norm_num [OrdinaryGFApplicationsBudgetCertificate.budgetControlled,
      sampleOrdinaryGFApplicationsBudgetCertificate]

example :
    sampleOrdinaryGFApplicationsBudgetCertificate.certificateBudgetWindow ≤
      sampleOrdinaryGFApplicationsBudgetCertificate.size := by
  apply ordinaryGFApplications_budgetCertificate_le_size
  constructor
  · norm_num [OrdinaryGFApplicationsBudgetCertificate.controlled,
      sampleOrdinaryGFApplicationsBudgetCertificate]
  · norm_num [OrdinaryGFApplicationsBudgetCertificate.budgetControlled,
      sampleOrdinaryGFApplicationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleOrdinaryGFApplicationsBudgetCertificate.Ready := by
  constructor
  · norm_num [OrdinaryGFApplicationsBudgetCertificate.controlled,
      sampleOrdinaryGFApplicationsBudgetCertificate]
  · norm_num [OrdinaryGFApplicationsBudgetCertificate.budgetControlled,
      sampleOrdinaryGFApplicationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleOrdinaryGFApplicationsBudgetCertificate.certificateBudgetWindow ≤
      sampleOrdinaryGFApplicationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List OrdinaryGFApplicationsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleOrdinaryGFApplicationsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleOrdinaryGFApplicationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.OrdinaryGFApplications
