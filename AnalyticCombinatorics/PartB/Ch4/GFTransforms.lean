import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.GFTransforms


/-!
Chapter IV generating-function transforms, stated as finite coefficient
identities.  The finite checks below model ordinary/exponential coefficients,
Euler products, Lambert-series coefficient extraction, and the arithmetic
inversions used in the inverse Euler transform.
-/

open Finset

/-! ## Basic finite coefficient operations -/

def factorialQ (n : ℕ) : ℚ := (Nat.factorial n : ℚ)

def dividesBool (d n : ℕ) : Bool := d ≠ 0 && n % d = 0

def allParts (_ : ℕ) : Bool := true

def oddParts (k : ℕ) : Bool := k % 2 = 1

/-- Coefficient of `z^n` in `∏_{k=1}^{maxPart} (1-z^k)^{-1}` with an
optional part filter. -/
def unrestrictedProductCoeff (allowed : ℕ → Bool) (n : ℕ) : ℕ → ℕ
  | 0 => if n = 0 then 1 else 0
  | maxPart + 1 =>
      if allowed (maxPart + 1) then
        ∑ m ∈ Finset.range (n / (maxPart + 1) + 1),
          unrestrictedProductCoeff allowed (n - m * (maxPart + 1)) maxPart
      else
        unrestrictedProductCoeff allowed n maxPart

/-- Coefficient of `z^n` in `∏_{k=1}^{maxPart} (1+z^k)` with an optional
part filter. -/
def restrictedProductCoeff (allowed : ℕ → Bool) (n : ℕ) : ℕ → ℕ
  | 0 => if n = 0 then 1 else 0
  | maxPart + 1 =>
      restrictedProductCoeff allowed n maxPart +
        if allowed (maxPart + 1) && maxPart + 1 ≤ n then
          restrictedProductCoeff allowed (n - (maxPart + 1)) maxPart
        else
          0

def partitionNumber (n : ℕ) : ℕ :=
  unrestrictedProductCoeff allParts n n

def distinctPartitionNumber (n : ℕ) : ℕ :=
  restrictedProductCoeff allParts n n

def oddPartitionNumber (n : ℕ) : ℕ :=
  unrestrictedProductCoeff oddParts n n

/-! ## 1. Euler transform: restricted and unrestricted partition GFs -/

/-- Euler's distinct/odd partition identity, at the coefficient level:
`∏(1+z^k) = ∏(1-z^(2k))/(1-z^k) = ∏_{k odd}(1-z^k)^{-1}`. -/
theorem euler_distinct_partitions_eq_odd_partitions_upto_twelve :
    List.ofFn (fun n : Fin 13 => distinctPartitionNumber n.val) =
      List.ofFn (fun n : Fin 13 => oddPartitionNumber n.val) := by
  native_decide

/-- The shared coefficients of the restricted and odd unrestricted products. -/
theorem euler_distinct_odd_coefficients_upto_twelve :
    List.ofFn (fun n : Fin 13 => distinctPartitionNumber n.val) =
      [1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15] := by
  native_decide

/-! ## 2. Borel transform: `a n / n! ↔ a n` -/

def borelCoeff (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  a n / factorialQ n

def inverseBorelCoeff (b : ℕ → ℚ) (n : ℕ) : ℚ :=
  b n * factorialQ n

def allOnesQ (_ : ℕ) : ℚ := 1

def expCoeff (n : ℕ) : ℚ := 1 / factorialQ n

/-- The Borel transform of the OGF with coefficients `1,1,1,...` has the
coefficients of `exp z`. -/
theorem borel_all_ones_is_exp_coefficients_upto_eight :
    List.ofFn (fun n : Fin 9 => borelCoeff allOnesQ n.val) =
      List.ofFn (fun n : Fin 9 => expCoeff n.val) := by
  native_decide

/-- Applying the inverse Borel transform recovers `1,1,1,...`. -/
theorem inverse_borel_exp_coefficients_upto_eight :
    List.ofFn (fun n : Fin 9 => inverseBorelCoeff expCoeff n.val) =
      [1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  native_decide

/-! ## 3. Inverse Euler transform: Möbius inversion on GF logarithms -/

def primeBool (n : ℕ) : Bool :=
  2 ≤ n && (List.range (n + 1)).all fun d => d < 2 || n % d ≠ 0 || d = n

def squarefreeBool (n : ℕ) : Bool :=
  (List.range (n + 1)).all fun p => !primeBool p || n % (p * p) ≠ 0

def primeDivisorCount (n : ℕ) : ℕ :=
  ((List.range (n + 1)).filter fun p => primeBool p && n % p = 0).length

def mobius (n : ℕ) : ℤ :=
  if n = 1 then
    1
  else if squarefreeBool n then
    if primeDivisorCount n % 2 = 0 then 1 else -1
  else
    0

def divisorSumInt (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ Finset.range (n + 1), if dividesBool d n then a d else 0

def mobiusInverse (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ Finset.range (n + 1), if dividesBool d n then mobius d * b (n / d) else 0

def eulerLogCoeff (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ Finset.range (n + 1), if dividesBool d n then (d : ℤ) * a d else 0

def inverseEulerCoeff (c : ℕ → ℤ) (n : ℕ) : ℤ :=
  mobiusInverse c n / (n : ℤ)

def onesZ (_ : ℕ) : ℤ := 1

def idZ (n : ℕ) : ℤ := n

/-- Ordinary Möbius inversion for divisor sums, checked on `a_n = n`. -/
theorem mobius_inversion_divisor_sums_upto_twelve :
    List.ofFn (fun i : Fin 12 => mobiusInverse (divisorSumInt idZ) (i.val + 1)) =
      List.ofFn (fun i : Fin 12 => idZ (i.val + 1)) := by
  native_decide

/-- Inverse Euler transform: from `z F'(z)/F(z)` coefficients
`c_n = ∑_{d|n} d a_d`, recover `a_n`. -/
theorem inverse_euler_recovers_all_ones_upto_twelve :
    List.ofFn (fun i : Fin 12 => inverseEulerCoeff (eulerLogCoeff onesZ) (i.val + 1)) =
      List.ofFn (fun _ : Fin 12 => (1 : ℤ)) := by
  native_decide

/-! ## 4. Exponential to ordinary: multiply EGF coefficients by `n!` -/

def egfToOrdCoeff (b : ℕ → ℚ) (n : ℕ) : ℚ :=
  b n * factorialQ n

def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)

def bellNumber (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), stirling2 n k

def bellEgfCoeff (n : ℕ) : ℚ :=
  (bellNumber n : ℚ) / factorialQ n

/-- Bell-number EGF coefficients convert back to ordinary coefficients by
multiplication by `n!`. -/
theorem bell_exponential_to_ordinary_upto_seven :
    List.ofFn (fun n : Fin 8 => egfToOrdCoeff bellEgfCoeff n.val) =
      List.ofFn (fun n : Fin 8 => (bellNumber n.val : ℚ)) := by
  native_decide

theorem bell_numbers_upto_seven :
    List.ofFn (fun n : Fin 8 => bellNumber n.val) =
      [1, 1, 2, 5, 15, 52, 203, 877] := by
  native_decide

/-! ## 5. Multiset construction: partition coefficients -/

/-- The multiset construction over one atom of each positive size gives
`∏_{k≥1} 1/(1-z^k)`, whose coefficients are the partition numbers. -/
theorem multiset_product_coefficients_are_partition_numbers_upto_twelve :
    List.ofFn (fun n : Fin 13 => unrestrictedProductCoeff allParts n.val n.val) =
      List.ofFn (fun n : Fin 13 => partitionNumber n.val) := by
  native_decide

theorem partition_numbers_upto_twelve :
    List.ofFn (fun n : Fin 13 => partitionNumber n.val) =
      [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77] := by
  native_decide

/-! ## 6. Dirichlet series to ordinary GF: Lambert coefficient extraction -/

/-- Coefficient of `z^n` in the finite Lambert series
`∑_{k≤maxK} a_k z^k/(1-z^k)`, expanded through `maxM` multiples. -/
def lambertExpandedCoeff (a : ℕ → ℤ) (n maxK maxM : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (maxK + 1),
    ∑ m ∈ Finset.range (maxM + 1),
      if k * (m + 1) = n then a k else 0

/-- Coefficient of `z^n` in `∑ k a_k z^k/(1-z^k)`. -/
def weightedLambertExpandedCoeff (a : ℕ → ℤ) (n maxK maxM : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (maxK + 1),
    ∑ m ∈ Finset.range (maxM + 1),
      if k * (m + 1) = n then (k : ℤ) * a k else 0

/-- `[z^n] ∑ a_k z^k/(1-z^k) = ∑_{d|n} a_d`, checked for `a_k = k`. -/
theorem lambert_coefficients_are_divisor_sums_upto_twelve :
    List.ofFn (fun i : Fin 12 =>
        lambertExpandedCoeff idZ (i.val + 1) (i.val + 1) (i.val + 1)) =
      List.ofFn (fun i : Fin 12 => divisorSumInt idZ (i.val + 1)) := by
  native_decide

/-- `[z^n] ∑ k a_k z^k/(1-z^k) = ∑_{d|n} d a_d`, checked for `a_k = 1`. -/
theorem weighted_lambert_coefficients_are_euler_log_coefficients_upto_twelve :
    List.ofFn (fun i : Fin 12 =>
        weightedLambertExpandedCoeff onesZ (i.val + 1) (i.val + 1) (i.val + 1)) =
      List.ofFn (fun i : Fin 12 => eulerLogCoeff onesZ (i.val + 1)) := by
  native_decide



structure GFTransformsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GFTransformsBudgetCertificate.controlled
    (c : GFTransformsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def GFTransformsBudgetCertificate.budgetControlled
    (c : GFTransformsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def GFTransformsBudgetCertificate.Ready
    (c : GFTransformsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GFTransformsBudgetCertificate.size
    (c : GFTransformsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem gFTransforms_budgetCertificate_le_size
    (c : GFTransformsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGFTransformsBudgetCertificate :
    GFTransformsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleGFTransformsBudgetCertificate.Ready := by
  constructor
  · norm_num [GFTransformsBudgetCertificate.controlled,
      sampleGFTransformsBudgetCertificate]
  · norm_num [GFTransformsBudgetCertificate.budgetControlled,
      sampleGFTransformsBudgetCertificate]

example :
    sampleGFTransformsBudgetCertificate.certificateBudgetWindow ≤
      sampleGFTransformsBudgetCertificate.size := by
  apply gFTransforms_budgetCertificate_le_size
  constructor
  · norm_num [GFTransformsBudgetCertificate.controlled,
      sampleGFTransformsBudgetCertificate]
  · norm_num [GFTransformsBudgetCertificate.budgetControlled,
      sampleGFTransformsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleGFTransformsBudgetCertificate.Ready := by
  constructor
  · norm_num [GFTransformsBudgetCertificate.controlled,
      sampleGFTransformsBudgetCertificate]
  · norm_num [GFTransformsBudgetCertificate.budgetControlled,
      sampleGFTransformsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGFTransformsBudgetCertificate.certificateBudgetWindow ≤
      sampleGFTransformsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List GFTransformsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGFTransformsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleGFTransformsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.GFTransforms
