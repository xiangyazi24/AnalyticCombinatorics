import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.FibonacciIdentities


open Finset

/-!
Finite Lean checks for the Fibonacci and Lucas identities appearing in
Chapter I of Flajolet and Sedgewick.
-/

/-! ## Fibonacci numbers -/

/-- Fibonacci numbers with `F(0)=0`, `F(1)=1`. -/
def F : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => F (n + 1) + F n

theorem fibonacci_zero : F 0 = 0 := by
  native_decide

theorem fibonacci_one : F 1 = 1 := by
  native_decide

theorem fibonacci_recurrence_0_20 :
    ∀ n : Fin 21, F (n.1 + 2) = F (n.1 + 1) + F n.1 := by
  native_decide

theorem fibonacci_values_0_15 :
    [F 0, F 1, F 2, F 3, F 4, F 5, F 6, F 7,
      F 8, F 9, F 10, F 11, F 12, F 13, F 14, F 15] =
    [0, 1, 1, 2, 3, 5, 8, 13,
      21, 34, 55, 89, 144, 233, 377, 610] := by
  native_decide

/-! ## Lucas numbers -/

/-- Lucas numbers with `L(0)=2`, `L(1)=1`. -/
def L : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => L (n + 1) + L n

theorem lucas_zero : L 0 = 2 := by
  native_decide

theorem lucas_one : L 1 = 1 := by
  native_decide

theorem lucas_recurrence_0_20 :
    ∀ n : Fin 21, L (n.1 + 2) = L (n.1 + 1) + L n.1 := by
  native_decide

theorem lucas_values_0_10 :
    [L 0, L 1, L 2, L 3, L 4, L 5,
      L 6, L 7, L 8, L 9, L 10] =
    [2, 1, 3, 4, 7, 11,
      18, 29, 47, 76, 123] := by
  native_decide

/-! ## Cassini's identity -/

/-- Integer-valued Cassini difference:
`F(n-1) * F(n+1) - F(n)^2`. -/
def cassiniDiff (n : ℕ) : ℤ :=
  ((F (n - 1) * F (n + 1) : ℕ) : ℤ) - ((F n ^ 2 : ℕ) : ℤ)

theorem cassini_signed_values_2_10 :
    [cassiniDiff 2, cassiniDiff 3, cassiniDiff 4, cassiniDiff 5,
      cassiniDiff 6, cassiniDiff 7, cassiniDiff 8, cassiniDiff 9,
      cassiniDiff 10] =
    [1, -1, 1, -1, 1, -1, 1, -1, 1] := by
  native_decide

theorem cassini_forms_2_10 :
    F 1 * F 3 = F 2 ^ 2 + 1 ∧
    F 2 * F 4 = F 3 ^ 2 - 1 ∧
    F 3 * F 5 = F 4 ^ 2 + 1 ∧
    F 4 * F 6 = F 5 ^ 2 - 1 ∧
    F 5 * F 7 = F 6 ^ 2 + 1 ∧
    F 6 * F 8 = F 7 ^ 2 - 1 ∧
    F 7 * F 9 = F 8 ^ 2 + 1 ∧
    F 8 * F 10 = F 9 ^ 2 - 1 ∧
    F 9 * F 11 = F 10 ^ 2 + 1 := by
  native_decide

/-! ## Sum identity -/

theorem fibonacci_sum_identity_0_10 :
    ∀ n : Fin 11, (∑ k ∈ Finset.range (n.1 + 1), F k) = F (n.1 + 2) - 1 := by
  native_decide

theorem fibonacci_sum_values_0_10 :
    [(∑ k ∈ Finset.range (0 + 1), F k),
      (∑ k ∈ Finset.range (1 + 1), F k),
      (∑ k ∈ Finset.range (2 + 1), F k),
      (∑ k ∈ Finset.range (3 + 1), F k),
      (∑ k ∈ Finset.range (4 + 1), F k),
      (∑ k ∈ Finset.range (5 + 1), F k),
      (∑ k ∈ Finset.range (6 + 1), F k),
      (∑ k ∈ Finset.range (7 + 1), F k),
      (∑ k ∈ Finset.range (8 + 1), F k),
      (∑ k ∈ Finset.range (9 + 1), F k),
      (∑ k ∈ Finset.range (10 + 1), F k)] =
    [0, 1, 2, 4, 7, 12, 20, 33, 54, 88, 143] := by
  native_decide

/-! ## GCD and divisibility checks -/

theorem fibonacci_gcd_property_0_10 :
    ∀ m : Fin 11, ∀ n : Fin 11,
      Nat.gcd (F m.1) (F n.1) = F (Nat.gcd m.1 n.1) := by
  native_decide

theorem fibonacci_gcd_selected_pairs :
    Nat.gcd (F 6) (F 9) = F (Nat.gcd 6 9) ∧
    Nat.gcd (F 8) (F 10) = F (Nat.gcd 8 10) ∧
    Nat.gcd (F 9) (F 10) = F (Nat.gcd 9 10) ∧
    Nat.gcd (F 10) (F 15) = F (Nat.gcd 10 15) := by
  native_decide

theorem fibonacci_divisibility_3_4_5_by_2_3 :
    F 3 ∣ F (2 * 3) ∧
    F 3 ∣ F (3 * 3) ∧
    F 4 ∣ F (2 * 4) ∧
    F 4 ∣ F (3 * 4) ∧
    F 5 ∣ F (2 * 5) ∧
    F 5 ∣ F (3 * 5) := by
  native_decide

/-! ## Zeckendorf checks -/

/--
Value represented by a bitmask selecting terms from
`F(2), F(3), ..., F(width+1)`.
-/
def zeckendorfMaskValue (width mask : ℕ) : ℕ :=
  ∑ i ∈ Finset.range width, if Nat.testBit mask i then F (i + 2) else 0

/--
Auxiliary Boolean test that no adjacent bits among
`0, ..., checked` are simultaneously set.
-/
def noAdjacentAux (mask : ℕ) : ℕ → Bool
  | 0 => true
  | i + 1 => noAdjacentAux mask i && !(Nat.testBit mask i && Nat.testBit mask (i + 1))

/-- Boolean nonconsecutiveness test for Zeckendorf bitmasks. -/
def zeckendorfMaskNonconsecutive (width mask : ℕ) : Bool :=
  noAdjacentAux mask (width - 1)

/-- Boolean predicate for a Zeckendorf representation of `target`. -/
def zeckendorfMaskRep (width target mask : ℕ) : Bool :=
  zeckendorfMaskNonconsecutive width mask && (zeckendorfMaskValue width mask == target)

/--
Number of nonconsecutive bitmask representations of `target` using
`F(2), ..., F(width+1)`.
-/
def zeckendorfRepCount (width target : ℕ) : ℕ :=
  (Finset.univ.filter fun mask : Fin (2 ^ width) =>
    zeckendorfMaskRep width target mask.1).card

theorem zeckendorf_unique_positive_1_30 :
    ∀ n : Fin 30, zeckendorfRepCount 8 (n.1 + 1) = 1 := by
  native_decide

theorem zeckendorf_counts_1_10 :
    [zeckendorfRepCount 8 1, zeckendorfRepCount 8 2,
      zeckendorfRepCount 8 3, zeckendorfRepCount 8 4,
      zeckendorfRepCount 8 5, zeckendorfRepCount 8 6,
      zeckendorfRepCount 8 7, zeckendorfRepCount 8 8,
      zeckendorfRepCount 8 9, zeckendorfRepCount 8 10] =
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  native_decide



structure FibonacciIdentitiesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FibonacciIdentitiesBudgetCertificate.controlled
    (c : FibonacciIdentitiesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FibonacciIdentitiesBudgetCertificate.budgetControlled
    (c : FibonacciIdentitiesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FibonacciIdentitiesBudgetCertificate.Ready
    (c : FibonacciIdentitiesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FibonacciIdentitiesBudgetCertificate.size
    (c : FibonacciIdentitiesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem fibonacciIdentities_budgetCertificate_le_size
    (c : FibonacciIdentitiesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFibonacciIdentitiesBudgetCertificate :
    FibonacciIdentitiesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFibonacciIdentitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [FibonacciIdentitiesBudgetCertificate.controlled,
      sampleFibonacciIdentitiesBudgetCertificate]
  · norm_num [FibonacciIdentitiesBudgetCertificate.budgetControlled,
      sampleFibonacciIdentitiesBudgetCertificate]

example :
    sampleFibonacciIdentitiesBudgetCertificate.certificateBudgetWindow ≤
      sampleFibonacciIdentitiesBudgetCertificate.size := by
  apply fibonacciIdentities_budgetCertificate_le_size
  constructor
  · norm_num [FibonacciIdentitiesBudgetCertificate.controlled,
      sampleFibonacciIdentitiesBudgetCertificate]
  · norm_num [FibonacciIdentitiesBudgetCertificate.budgetControlled,
      sampleFibonacciIdentitiesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFibonacciIdentitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [FibonacciIdentitiesBudgetCertificate.controlled,
      sampleFibonacciIdentitiesBudgetCertificate]
  · norm_num [FibonacciIdentitiesBudgetCertificate.budgetControlled,
      sampleFibonacciIdentitiesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFibonacciIdentitiesBudgetCertificate.certificateBudgetWindow ≤
      sampleFibonacciIdentitiesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FibonacciIdentitiesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFibonacciIdentitiesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFibonacciIdentitiesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.FibonacciIdentities
