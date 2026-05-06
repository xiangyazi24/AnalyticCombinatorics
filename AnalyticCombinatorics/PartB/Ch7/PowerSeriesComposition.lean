import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch7.PowerSeriesComposition


open scoped BigOperators

/-!
# Power series composition and reversion

Finite executable checks inspired by Chapter VII of Flajolet and Sedgewick:
composition of exponential generating functions, small reversion coefficients,
Faà di Bruno coefficients, and the labelled tree function `W = x * exp W`.
-/

def coeffPowerQ (a : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, k => if k = 0 then 1 else 0
  | p + 1, k => ∑ i ∈ Finset.range (k + 1), a i * coeffPowerQ a p (k - i)

def expOfSeriesCoeff (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ p ∈ Finset.range (n + 1), coeffPowerQ a p n / (Nat.factorial p : ℚ)

def stirlingSecond : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k

def bellNumber (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), stirlingSecond n k

def bellTable : Fin 11 → ℕ :=
  ![1, 1, 2, 5, 15, 52, 203, 877, 4140, 21147, 115975]

def expMinusOneCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else 1 / (Nat.factorial n : ℚ)

def bellEgfCoeff (n : ℕ) : ℚ :=
  (bellNumber n : ℚ) / (Nat.factorial n : ℚ)

theorem bellTable_matches_sum :
    ∀ n : Fin 11, bellTable n = bellNumber n.val := by
  native_decide

theorem bell_egf_is_exp_exp_minus_one :
    ∀ n : Fin 9, expOfSeriesCoeff expMinusOneCoeff n.val = bellEgfCoeff n.val := by
  native_decide

theorem bell_first_coefficients :
    [bellNumber 0, bellNumber 1, bellNumber 2, bellNumber 3, bellNumber 4,
      bellNumber 5, bellNumber 6] = [1, 1, 2, 5, 15, 52, 203] := by
  native_decide

def oddDoubleFactorialPrefix (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.range n, (2 * k + 1)

def inverseQuadraticCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else (oddDoubleFactorialPrefix (n - 1) : ℚ) / (Nat.factorial n : ℚ)

def inverseQuadraticScaledTable : Fin 8 → ℕ :=
  ![1, 1, 3, 15, 105, 945, 10395, 135135]

def quadraticForwardOfInverseCoeff (n : ℕ) : ℚ :=
  inverseQuadraticCoeff n - coeffPowerQ inverseQuadraticCoeff 2 n / 2

theorem inverseQuadratic_scaled_table :
    ∀ n : Fin 8,
      inverseQuadraticScaledTable n = oddDoubleFactorialPrefix n.val := by
  native_decide

theorem inverseQuadratic_reverts_x_sub_x2_over_two :
    ∀ n : Fin 9,
      quadraticForwardOfInverseCoeff n.val = if n.val = 1 then 1 else 0 := by
  native_decide

theorem inverseQuadratic_first_terms :
    [inverseQuadraticCoeff 1, inverseQuadraticCoeff 2, inverseQuadraticCoeff 3,
      inverseQuadraticCoeff 4, inverseQuadraticCoeff 5] =
      [1, 1 / 2, 1 / 2, 5 / 8, 7 / 8] := by
  native_decide

def profileWeight {n : ℕ} (p : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, (i.val + 1) * p i

def profileBlocks {n : ℕ} (p : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, p i

def bellProfileCoeff (n : ℕ) (p : Fin n → ℕ) : ℕ :=
  if profileWeight p = n then
    Nat.factorial n /
      ∏ i : Fin n, Nat.factorial (p i) * Nat.factorial (i.val + 1) ^ p i
  else
    0

def faaDiBrunoProfile4 (i : Fin 5) (j : Fin 4) : ℕ :=
  match i.val, j.val with
  | 0, 3 => 1
  | 1, 0 => 1
  | 1, 2 => 1
  | 2, 1 => 2
  | 3, 0 => 2
  | 3, 1 => 1
  | 4, 0 => 4
  | _, _ => 0

def faaDiBrunoN4CoeffTable : Fin 5 → ℕ :=
  ![1, 4, 3, 6, 1]

def faaDiBrunoN4ByBlocksTable : Fin 4 → ℕ :=
  ![1, 7, 6, 1]

def faaDiBrunoN4BlockSum (k : ℕ) : ℕ :=
  ∑ i : Fin 5,
    if profileBlocks (faaDiBrunoProfile4 i) = k then
      bellProfileCoeff 4 (faaDiBrunoProfile4 i)
    else
      0

theorem faaDiBruno_n4_profile_coefficients :
    ∀ i : Fin 5,
      faaDiBrunoN4CoeffTable i = bellProfileCoeff 4 (faaDiBrunoProfile4 i) := by
  native_decide

theorem faaDiBruno_n4_blocks :
    ∀ k : Fin 4,
      faaDiBrunoN4ByBlocksTable k = faaDiBrunoN4BlockSum (k.val + 1) := by
  native_decide

theorem faaDiBruno_n4_blocks_are_stirling :
    ∀ k : Fin 4,
      faaDiBrunoN4ByBlocksTable k = stirlingSecond 4 (k.val + 1) := by
  native_decide

def treeFunctionScaledCoeff (n : ℕ) : ℕ :=
  if n = 0 then 0 else n ^ (n - 1)

def treeFunctionCoeff (n : ℕ) : ℚ :=
  (treeFunctionScaledCoeff n : ℚ) / (Nat.factorial n : ℚ)

def treeFunctionScaledTable : Fin 8 → ℕ :=
  ![1, 2, 9, 64, 625, 7776, 117649, 2097152]

theorem treeFunction_scaled_table :
    ∀ n : Fin 8,
      treeFunctionScaledTable n = treeFunctionScaledCoeff (n.val + 1) := by
  native_decide

theorem treeFunction_satisfies_W_eq_x_exp_W :
    ∀ n : Fin 8,
      treeFunctionCoeff (n.val + 1) = expOfSeriesCoeff treeFunctionCoeff n.val := by
  native_decide

theorem treeFunction_first_terms :
    [treeFunctionCoeff 1, treeFunctionCoeff 2, treeFunctionCoeff 3,
      treeFunctionCoeff 4, treeFunctionCoeff 5] =
      [1, 1, 3 / 2, 8 / 3, 125 / 24] := by
  native_decide



structure PowerSeriesCompositionBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PowerSeriesCompositionBudgetCertificate.controlled
    (c : PowerSeriesCompositionBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PowerSeriesCompositionBudgetCertificate.budgetControlled
    (c : PowerSeriesCompositionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PowerSeriesCompositionBudgetCertificate.Ready
    (c : PowerSeriesCompositionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PowerSeriesCompositionBudgetCertificate.size
    (c : PowerSeriesCompositionBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem powerSeriesComposition_budgetCertificate_le_size
    (c : PowerSeriesCompositionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePowerSeriesCompositionBudgetCertificate :
    PowerSeriesCompositionBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePowerSeriesCompositionBudgetCertificate.Ready := by
  constructor
  · norm_num [PowerSeriesCompositionBudgetCertificate.controlled,
      samplePowerSeriesCompositionBudgetCertificate]
  · norm_num [PowerSeriesCompositionBudgetCertificate.budgetControlled,
      samplePowerSeriesCompositionBudgetCertificate]

example :
    samplePowerSeriesCompositionBudgetCertificate.certificateBudgetWindow ≤
      samplePowerSeriesCompositionBudgetCertificate.size := by
  apply powerSeriesComposition_budgetCertificate_le_size
  constructor
  · norm_num [PowerSeriesCompositionBudgetCertificate.controlled,
      samplePowerSeriesCompositionBudgetCertificate]
  · norm_num [PowerSeriesCompositionBudgetCertificate.budgetControlled,
      samplePowerSeriesCompositionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePowerSeriesCompositionBudgetCertificate.Ready := by
  constructor
  · norm_num [PowerSeriesCompositionBudgetCertificate.controlled,
      samplePowerSeriesCompositionBudgetCertificate]
  · norm_num [PowerSeriesCompositionBudgetCertificate.budgetControlled,
      samplePowerSeriesCompositionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePowerSeriesCompositionBudgetCertificate.certificateBudgetWindow ≤
      samplePowerSeriesCompositionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PowerSeriesCompositionBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePowerSeriesCompositionBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePowerSeriesCompositionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.PowerSeriesComposition
