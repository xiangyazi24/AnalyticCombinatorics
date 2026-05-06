import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.TransferApplications


/-!
Finite, computable coefficient checks for standard applications of
singularity transfer in Chapter VI of Flajolet and Sedgewick.

The analytic statements are represented here by their coefficient sequences.
All proofs are closed computations discharged by `native_decide`.
-/

/-! ## Poles at `z = 1` -/

/-- Coefficients of `(1 - z)^(-1)`. -/
def simplePoleCoeff (n : Nat) : Nat := n - n + 1

/-- Coefficients of `(1 - z)^(-2)`. -/
def doublePoleCoeff (n : Nat) : Nat := n + 1

/-- Coefficients of `(1 - z)^(-3)`. -/
def triplePoleCoeff (n : Nat) : Nat := Nat.choose (n + 2) 2

/-- Product form of the coefficients of `(1 - z)^(-3)`. -/
def triplePoleProductCoeff (n : Nat) : Nat := ((n + 1) * (n + 2)) / 2

theorem simple_pole_transfer_all (n : Nat) :
    simplePoleCoeff n = 1 := by
  simp [simplePoleCoeff]

theorem double_pole_transfer_up_to_8 :
    (List.range 9).map doublePoleCoeff = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide

theorem double_pole_formula_up_to_8 :
    ∀ n : Fin 9, doublePoleCoeff n = (n : Nat) + 1 := by
  native_decide

theorem triple_pole_transfer_up_to_8 :
    (List.range 9).map triplePoleCoeff = [1, 3, 6, 10, 15, 21, 28, 36, 45] := by
  native_decide

theorem triple_pole_product_formula_up_to_8 :
    ∀ n : Fin 9, triplePoleCoeff n = triplePoleProductCoeff n := by
  native_decide

/-! ## Square-root singularity model -/

/-- Central binomial coefficient `C(2n,n)`. -/
def centralBinom (n : Nat) : Nat := Nat.choose (2 * n) n

theorem central_binomial_values_up_to_8 :
    (List.range 9).map centralBinom =
      [1, 2, 6, 20, 70, 252, 924, 3432, 12870] := by
  native_decide

theorem central_binomial_cancel_up_to_8 :
    ∀ n : Fin 9,
      (4 ^ (n : Nat) * centralBinom n) / 4 ^ (n : Nat) = centralBinom n := by
  native_decide

theorem central_binomial_square_bound_is_false :
    ¬ centralBinom 1 ^ 2 < 4 ^ (1 : Nat) := by
  native_decide

theorem central_binomial_lt_four_pow_up_to_8 :
    ∀ n : Fin 8,
      centralBinom ((n : Nat) + 1) < 4 ^ ((n : Nat) + 1) := by
  native_decide

/-! ## Catalan transfer model -/

/-- Catalan number `C_n = binom(2n,n)/(n+1)`. -/
def catalan (n : Nat) : Nat := centralBinom n / (n + 1)

theorem catalan_values_up_to_8 :
    (List.range 9).map catalan = [1, 1, 2, 5, 14, 42, 132, 429, 1430] := by
  native_decide

/-- Numerator of `(C_n * sqrt n / 4^n)^2`. -/
def catalanSqrtRatioSqNum (n : Nat) : Nat := n * catalan n ^ 2

/-- Numerator of `(C_n * n^(3/2) / 4^n)^2`, the transfer scaling. -/
def catalanTransferRatioSqNum (n : Nat) : Nat := n ^ 3 * catalan n ^ 2

theorem catalan_sqrt_ratio_sq_bounds_1_to_8 :
    ∀ n : Fin 8,
      let k := (n : Nat) + 1
      16 ^ k ≤ 512 * catalanSqrtRatioSqNum k ∧
        16 * catalanSqrtRatioSqNum k ≤ 16 ^ k := by
  native_decide

theorem catalan_transfer_ratio_sq_bounds_1_to_8 :
    ∀ n : Fin 8,
      let k := (n : Nat) + 1
      16 ^ k ≤ 16 * catalanTransferRatioSqNum k ∧
        4 * catalanTransferRatioSqNum k ≤ 16 ^ k := by
  native_decide

/-! ## Fibonacci transfer model -/

/-- Fibonacci numbers with `F_0 = 0`, `F_1 = 1`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Pair `(a,b)` such that `(1 + sqrt 5)^n = a + b*sqrt 5`. -/
def goldenPowPair : Nat → Nat × Nat
  | 0 => (1, 0)
  | n + 1 =>
      let p := goldenPowPair n
      (p.1 + 5 * p.2, p.1 + p.2)

/--
Boolean integer certificate for `phi^n > m`, where `phi = (1 + sqrt 5)/2`.
For `(1 + sqrt 5)^n = a + b*sqrt 5`, it decides
`a + b*sqrt 5 > 2^n*m` by squaring only after isolating the radical.
-/
def goldenPowGTNat (n m : Nat) : Bool :=
  let p := goldenPowPair n
  let target := 2 ^ n * m
  if target ≤ p.1 then true else decide ((target - p.1) ^ 2 < 5 * p.2 ^ 2)

theorem fibonacci_values_up_to_12 :
    (List.range 13).map fib = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144] := by
  native_decide

theorem fibonacci_phi_dominates_up_to_20 :
    ∀ n : Fin 20,
      let k := (n : Nat) + 1
      goldenPowGTNat k (fib k) = true := by
  native_decide

theorem fibonacci_phi_integer_certificate_up_to_20 :
    ∀ n : Fin 20,
      let k := (n : Nat) + 1
      let p := goldenPowPair k
      let target := 2 ^ k * fib k
      target ≤ p.1 ∨ (target - p.1) ^ 2 < 5 * p.2 ^ 2 := by
  native_decide



structure TransferApplicationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransferApplicationsBudgetCertificate.controlled
    (c : TransferApplicationsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TransferApplicationsBudgetCertificate.budgetControlled
    (c : TransferApplicationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TransferApplicationsBudgetCertificate.Ready
    (c : TransferApplicationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TransferApplicationsBudgetCertificate.size
    (c : TransferApplicationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem transferApplications_budgetCertificate_le_size
    (c : TransferApplicationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTransferApplicationsBudgetCertificate :
    TransferApplicationsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleTransferApplicationsBudgetCertificate.Ready := by
  constructor
  · norm_num [TransferApplicationsBudgetCertificate.controlled,
      sampleTransferApplicationsBudgetCertificate]
  · norm_num [TransferApplicationsBudgetCertificate.budgetControlled,
      sampleTransferApplicationsBudgetCertificate]

example :
    sampleTransferApplicationsBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferApplicationsBudgetCertificate.size := by
  apply transferApplications_budgetCertificate_le_size
  constructor
  · norm_num [TransferApplicationsBudgetCertificate.controlled,
      sampleTransferApplicationsBudgetCertificate]
  · norm_num [TransferApplicationsBudgetCertificate.budgetControlled,
      sampleTransferApplicationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTransferApplicationsBudgetCertificate.Ready := by
  constructor
  · norm_num [TransferApplicationsBudgetCertificate.controlled,
      sampleTransferApplicationsBudgetCertificate]
  · norm_num [TransferApplicationsBudgetCertificate.budgetControlled,
      sampleTransferApplicationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTransferApplicationsBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferApplicationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List TransferApplicationsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTransferApplicationsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTransferApplicationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.TransferApplications
