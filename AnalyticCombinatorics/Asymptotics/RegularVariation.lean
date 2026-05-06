import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Regular variation windows.
-/

namespace AnalyticCombinatorics.Asymptotics.RegularVariation

/-- Power model for a regularly varying sequence of integral index. -/
def powerModel (alpha n : ℕ) : ℕ :=
  n ^ alpha

/-- Finite positivity check away from the origin. -/
def positiveAfterUpTo (a : ℕ → ℕ) (n0 N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n < n0 then true else 0 < a n

/--
Finite dyadic regular-variation window.  The cross-multiplied form avoids
division and gives a robust certificate that `a (2n)` has index `alpha`
relative to `a n`, up to a factor of two.
-/
def dyadicRegularVariationCheck
    (a : ℕ → ℕ) (alpha N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n = 0 then true
    else
      a (2 * n) ≤ 2 ^ (alpha + 1) * a n ∧
        2 ^ alpha * a n ≤ 2 * a (2 * n)

/-- Finite regular-variation statement for sampled sequences. -/
def RegularVariationWindow
    (a : ℕ → ℕ) (alpha N : ℕ) : Prop :=
  positiveAfterUpTo a 1 N = true ∧
    dyadicRegularVariationCheck a alpha N = true

theorem powerModel_regularVariation_alpha_zero :
    RegularVariationWindow (powerModel 0) 0 24 := by
  unfold RegularVariationWindow positiveAfterUpTo dyadicRegularVariationCheck
    powerModel
  native_decide

theorem powerModel_regularVariation_alpha_one :
    RegularVariationWindow (powerModel 1) 1 24 := by
  unfold RegularVariationWindow positiveAfterUpTo dyadicRegularVariationCheck
    powerModel
  native_decide

theorem powerModel_regularVariation_alpha_two :
    RegularVariationWindow (powerModel 2) 2 24 := by
  unfold RegularVariationWindow positiveAfterUpTo dyadicRegularVariationCheck
    powerModel
  native_decide

example : powerModel 3 4 = 64 := by
  unfold powerModel
  native_decide

example : dyadicRegularVariationCheck (powerModel 2) 2 8 = true := by
  unfold dyadicRegularVariationCheck powerModel
  native_decide

structure RegularVariationBudgetCertificate where
  indexWindow : ℕ
  scaleWindow : ℕ
  comparisonWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularVariationBudgetCertificate.controlled
    (c : RegularVariationBudgetCertificate) : Prop :=
  0 < c.indexWindow ∧
    c.comparisonWindow ≤ c.indexWindow + c.scaleWindow + c.slack

def RegularVariationBudgetCertificate.budgetControlled
    (c : RegularVariationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.indexWindow + c.scaleWindow + c.comparisonWindow + c.slack

def RegularVariationBudgetCertificate.Ready
    (c : RegularVariationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RegularVariationBudgetCertificate.size
    (c : RegularVariationBudgetCertificate) : ℕ :=
  c.indexWindow + c.scaleWindow + c.comparisonWindow + c.slack

theorem regularVariation_budgetCertificate_le_size
    (c : RegularVariationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleRegularVariationBudgetCertificate :
    RegularVariationBudgetCertificate :=
  { indexWindow := 5
    scaleWindow := 6
    comparisonWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example : sampleRegularVariationBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularVariationBudgetCertificate.controlled,
      sampleRegularVariationBudgetCertificate]
  · norm_num [RegularVariationBudgetCertificate.budgetControlled,
      sampleRegularVariationBudgetCertificate]

/-- Finite executable readiness audit for regular variation certificates. -/
def regularVariationCertificateListReady
    (certs : List RegularVariationBudgetCertificate) : Bool :=
  certs.all fun c =>
    0 < c.indexWindow &&
      c.comparisonWindow ≤ c.indexWindow + c.scaleWindow + c.slack &&
        c.certificateBudgetWindow ≤
          c.indexWindow + c.scaleWindow + c.comparisonWindow + c.slack

theorem regularVariationCertificateList_readyWindow :
    regularVariationCertificateListReady
      [{ indexWindow := 3, scaleWindow := 4, comparisonWindow := 6,
         certificateBudgetWindow := 13, slack := 0 },
       { indexWindow := 5, scaleWindow := 6, comparisonWindow := 10,
         certificateBudgetWindow := 22, slack := 1 }] = true := by
  unfold regularVariationCertificateListReady
  native_decide

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

def budgetCertificateListReady
    (data : List RegularVariationBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRegularVariationBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRegularVariationBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.RegularVariation
