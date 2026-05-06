import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.BinomialTransforms


/-!
Finite-table checks for binomial transforms and Pascal-triangle identities.
-/

/-! ## Pascal row sums -/

def rowSum (n : ℕ) : ℕ :=
  ∑ k : Fin (n + 1), Nat.choose n k.val

def twoPowTable : Fin 13 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]

theorem twoPowTable_values :
    ∀ n : Fin 13, twoPowTable n = 2 ^ n.val := by
  native_decide

theorem pascal_row_sums_0_12 :
    ∀ n : Fin 13, rowSum n.val = twoPowTable n := by
  native_decide

theorem pascal_row_sums_eq_two_pow_0_12 :
    ∀ n : Fin 13, rowSum n.val = 2 ^ n.val := by
  native_decide

/-! ## Alternating row sums -/

def alternatingRowSum (n : ℕ) : ℤ :=
  ∑ k : Fin (n + 1), (-1 : ℤ) ^ k.val * (Nat.choose n k.val : ℤ)

def evenIndexSum (n : ℕ) : ℕ :=
  ∑ k : Fin (n + 1), if k.val % 2 = 0 then Nat.choose n k.val else 0

def oddIndexSum (n : ℕ) : ℕ :=
  ∑ k : Fin (n + 1), if k.val % 2 = 1 then Nat.choose n k.val else 0

def alternatingRows : Fin 4 → ℕ :=
  ![4, 6, 8, 10]

theorem alternating_row_sums_zero_1_12 :
    ∀ n : Fin 12, alternatingRowSum (n.val + 1) = 0 := by
  native_decide

theorem even_odd_row_sums_4_6_8_10 :
    ∀ i : Fin 4,
      evenIndexSum (alternatingRows i) = 2 ^ (alternatingRows i - 1) ∧
        oddIndexSum (alternatingRows i) = 2 ^ (alternatingRows i - 1) := by
  native_decide

/-! ## Hockey-stick identity -/

def hockeyR2Sum (n : ℕ) : ℕ :=
  ∑ k : Fin (n + 1), if 2 ≤ k.val then Nat.choose k.val 2 else 0

def hockeyRows : Fin 5 → ℕ :=
  ![4, 5, 6, 7, 8]

def hockeyValues : Fin 5 → ℕ :=
  ![10, 20, 35, 56, 84]

theorem hockey_stick_r2_4_8 :
    ∀ i : Fin 5,
      hockeyR2Sum (hockeyRows i) = Nat.choose (hockeyRows i + 1) 3 ∧
        Nat.choose (hockeyRows i + 1) 3 = hockeyValues i := by
  native_decide

/-! ## Vandermonde convolution -/

def vandermondeSum (m n r : ℕ) : ℕ :=
  ∑ k : Fin (r + 1), Nat.choose m k.val * Nat.choose n (r - k.val)

theorem vandermonde_5_5_5 :
    vandermondeSum 5 5 5 = Nat.choose (5 + 5) 5 ∧
      Nat.choose 10 5 = 252 := by
  native_decide

theorem vandermonde_4_4_4 :
    vandermondeSum 4 4 4 = Nat.choose (4 + 4) 4 ∧
      Nat.choose 8 4 = 70 := by
  native_decide

/-! ## Binomial inversion -/

def binomialTransform (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k : Fin (n + 1), (Nat.choose n k.val : ℤ) * a k.val

def binomialInverse (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k : Fin (n + 1),
    (-1 : ℤ) ^ (n - k.val) * (Nat.choose n k.val : ℤ) * b k.val

def oneSeq : ℕ → ℤ :=
  fun _ => 1

def twoPowSeq : ℕ → ℤ :=
  fun n => (2 : ℤ) ^ n

theorem binomial_transform_one_0_12 :
    ∀ n : Fin 13, binomialTransform oneSeq n.val = twoPowSeq n.val := by
  native_decide

def inversionRows : Fin 3 → ℕ :=
  ![2, 3, 4]

theorem binomial_inversion_one_2_4 :
    ∀ i : Fin 3, binomialInverse twoPowSeq (inversionRows i) = 1 := by
  native_decide

theorem binomial_inversion_n3_expansion :
    (-1 : ℤ) + 6 - 12 + 8 = 1 ∧
      binomialInverse twoPowSeq 3 = (-1 : ℤ) + 6 - 12 + 8 := by
  native_decide

/-! ## Upper summation -/

def upperSum (r n : ℕ) : ℕ :=
  ∑ k : Fin (n + 1), if r ≤ k.val then Nat.choose k.val r else 0

theorem upper_summation_r0_1_10 :
    ∀ i : Fin 10,
      upperSum 0 (i.val + 1) = i.val + 2 ∧
        upperSum 0 (i.val + 1) = Nat.choose (i.val + 2) 1 := by
  native_decide

theorem upper_summation_r1_1_10 :
    ∀ i : Fin 10,
      upperSum 1 (i.val + 1) = Nat.choose (i.val + 2) 2 ∧
        upperSum 1 (i.val + 1) = (i.val + 1) * (i.val + 2) / 2 := by
  native_decide



structure BinomialTransformsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BinomialTransformsBudgetCertificate.controlled
    (c : BinomialTransformsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BinomialTransformsBudgetCertificate.budgetControlled
    (c : BinomialTransformsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BinomialTransformsBudgetCertificate.Ready
    (c : BinomialTransformsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BinomialTransformsBudgetCertificate.size
    (c : BinomialTransformsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem binomialTransforms_budgetCertificate_le_size
    (c : BinomialTransformsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBinomialTransformsBudgetCertificate :
    BinomialTransformsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleBinomialTransformsBudgetCertificate.Ready := by
  constructor
  · norm_num [BinomialTransformsBudgetCertificate.controlled,
      sampleBinomialTransformsBudgetCertificate]
  · norm_num [BinomialTransformsBudgetCertificate.budgetControlled,
      sampleBinomialTransformsBudgetCertificate]

example :
    sampleBinomialTransformsBudgetCertificate.certificateBudgetWindow ≤
      sampleBinomialTransformsBudgetCertificate.size := by
  apply binomialTransforms_budgetCertificate_le_size
  constructor
  · norm_num [BinomialTransformsBudgetCertificate.controlled,
      sampleBinomialTransformsBudgetCertificate]
  · norm_num [BinomialTransformsBudgetCertificate.budgetControlled,
      sampleBinomialTransformsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBinomialTransformsBudgetCertificate.Ready := by
  constructor
  · norm_num [BinomialTransformsBudgetCertificate.controlled,
      sampleBinomialTransformsBudgetCertificate]
  · norm_num [BinomialTransformsBudgetCertificate.budgetControlled,
      sampleBinomialTransformsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBinomialTransformsBudgetCertificate.certificateBudgetWindow ≤
      sampleBinomialTransformsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BinomialTransformsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBinomialTransformsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBinomialTransformsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.BinomialTransforms
