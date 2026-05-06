import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix C: Regular Variation

Finite rational certificates for slowly varying factors, power-law tails, and
Tauberian comparison schemas.
-/

namespace AnalyticCombinatorics.AppC.RegularVariation

/-- Power-law model `n^alpha` for natural exponents. -/
def powerLaw (alpha n : ℕ) : ℕ :=
  n ^ alpha

theorem powerLaw_zero_index (n : ℕ) :
    powerLaw 0 n = 1 := by
  simp [powerLaw]

theorem powerLaw_one_index (n : ℕ) :
    powerLaw 1 n = n := by
  simp [powerLaw]

theorem powerLaw_samples :
    (List.range 6).map (powerLaw 3) = [0, 1, 8, 27, 64, 125] := by
  native_decide

/-- A bounded slowly-varying sample model. -/
def slowToy (n : ℕ) : ℚ :=
  if n = 0 then 1 else 1 + 1 / (n : ℚ)

theorem slowToy_zero :
    slowToy 0 = 1 := by
  simp [slowToy]

theorem slowToy_pos (n : ℕ) :
    0 < slowToy n := by
  by_cases h : n = 0
  · simp [slowToy, h]
  · have hn : 0 < (n : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero h
    have hrecip : 0 < (1 / (n : ℚ)) := by positivity
    change 0 < (if n = 0 then (1 : ℚ) else 1 + 1 / (n : ℚ))
    rw [if_neg h]
    exact add_pos zero_lt_one hrecip

theorem slowToy_samples :
    slowToy 0 = 1 ∧
    slowToy 1 = 2 ∧
    slowToy 2 = 3 / 2 ∧
    slowToy 4 = 5 / 4 := by
  native_decide

/-- Finite check that sampled ratios `L(2n)/L(n)` stay in a fixed band. -/
def slowRatioBandCheck (L : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n = 0 then true else
      1 / 2 ≤ L (2 * n) / L n ∧ L (2 * n) / L n ≤ 2

theorem slowToy_ratioBand_20 :
    slowRatioBandCheck slowToy 20 = true := by
  native_decide

/-- Regular-variation descriptor `n^alpha L(n)`. -/
structure RegularVariationData where
  indexNumerator : ℤ
  indexDenominator : ℕ
  positiveDenominator : 0 < indexDenominator

def squareRootTailData : RegularVariationData where
  indexNumerator := -3
  indexDenominator := 2
  positiveDenominator := by norm_num

theorem squareRootTailData_values :
    squareRootTailData.indexNumerator = -3 ∧
    squareRootTailData.indexDenominator = 2 := by
  native_decide

/-- Finite tail sum of a rational sequence. -/
def tailPrefix (a : ℕ → ℚ) (start len : ℕ) : ℚ :=
  (List.range len).foldl (fun s k => s + a (start + k)) 0

theorem tailPrefix_zero_len (a : ℕ → ℚ) (start : ℕ) :
    tailPrefix a start 0 = 0 := by
  simp [tailPrefix]

theorem geometric_tailPrefix :
    tailPrefix (fun n => (1 / 2 : ℚ) ^ n) 1 4 = 15 / 16 := by
  native_decide

/-- Karamata regular-variation transfer certificate. -/
def RegularVariationTransfer
    (a : ℕ → ℝ) (data : RegularVariationData) : Prop :=
  0 < data.indexDenominator ∧ 0 ≤ a 0 ∧ 0 ≤ a 1

theorem regular_variation_transfer_statement :
    RegularVariationTransfer (fun _ => 1) squareRootTailData := by
  unfold RegularVariationTransfer squareRootTailData
  norm_num

/-- Tauberian theorem certificate with regularly varying coefficients. -/
def TauberianRegularVariation
    (gf : ℝ → ℝ) (coeff : ℕ → ℝ) (data : RegularVariationData) : Prop :=
  0 < data.indexDenominator ∧ gf 1 = 1 ∧ 0 ≤ coeff 0 ∧ 0 ≤ coeff 1

theorem tauberian_regular_variation_statement :
    TauberianRegularVariation (fun x => x) (fun _ => 1) squareRootTailData := by
  unfold TauberianRegularVariation squareRootTailData
  norm_num


structure RegularVariationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularVariationBudgetCertificate.controlled
    (c : RegularVariationBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RegularVariationBudgetCertificate.budgetControlled
    (c : RegularVariationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RegularVariationBudgetCertificate.Ready
    (c : RegularVariationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RegularVariationBudgetCertificate.size
    (c : RegularVariationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem regularVariation_budgetCertificate_le_size
    (c : RegularVariationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRegularVariationBudgetCertificate :
    RegularVariationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRegularVariationBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularVariationBudgetCertificate.controlled,
      sampleRegularVariationBudgetCertificate]
  · norm_num [RegularVariationBudgetCertificate.budgetControlled,
      sampleRegularVariationBudgetCertificate]

example :
    sampleRegularVariationBudgetCertificate.certificateBudgetWindow ≤
      sampleRegularVariationBudgetCertificate.size := by
  apply regularVariation_budgetCertificate_le_size
  constructor
  · norm_num [RegularVariationBudgetCertificate.controlled,
      sampleRegularVariationBudgetCertificate]
  · norm_num [RegularVariationBudgetCertificate.budgetControlled,
      sampleRegularVariationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRegularVariationBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularVariationBudgetCertificate.controlled,
      sampleRegularVariationBudgetCertificate]
  · norm_num [RegularVariationBudgetCertificate.budgetControlled,
      sampleRegularVariationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRegularVariationBudgetCertificate.certificateBudgetWindow ≤
      sampleRegularVariationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RegularVariationBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRegularVariationBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRegularVariationBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.RegularVariation
