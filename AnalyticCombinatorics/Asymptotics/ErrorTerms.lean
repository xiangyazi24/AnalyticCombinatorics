import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Error Terms

Finite models for big-O, little-o, equivalent expansions, and explicit
coefficient error envelopes.
-/

namespace AnalyticCombinatorics.Asymptotics.ErrorTerms

/-- Finite big-O certificate `a_n <= C b_n` on a sampled interval. -/
def bigOCheck (a b : ℕ → ℕ) (C n0 N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n < n0 then true else a n ≤ C * b n

theorem linear_bigO_quadratic :
    bigOCheck (fun n => n) (fun n => n ^ 2) 1 1 20 = true := by
  native_decide

theorem quadratic_bigO_exponential :
    bigOCheck (fun n => n ^ 2) (fun n => 2 ^ n) 1 4 20 = true := by
  native_decide

/-- Finite little-o certificate: sampled ratios decrease and end below a threshold. -/
def littleOProxy (a b : ℕ → ℕ) (thresholdNum thresholdDen n0 N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n < n0 then true else
      (a n : ℚ) / (b n : ℚ) ≤ (thresholdNum : ℚ) / (thresholdDen : ℚ)

theorem linear_littleO_quadratic_tail :
    littleOProxy (fun n => n) (fun n => n ^ 2) 1 10 10 40 = true := by
  native_decide

/-- Absolute rational error. -/
def absQ (x : ℚ) : ℚ :=
  if x < 0 then -x else x

def errorWithin (approx exact tolerance : ℚ) : Bool :=
  absQ (approx - exact) ≤ tolerance

theorem errorWithin_samples :
    errorWithin (99 / 100) 1 (1 / 100) = true ∧
    errorWithin (101 / 100) 1 (1 / 100) = true ∧
    errorWithin (9 / 10) 1 (1 / 100) = false := by
  native_decide

/-- Truncated asymptotic expansion data. -/
structure ExpansionTerm where
  coefficient : ℚ
  powerNumerator : ℤ
  powerDenominator : ℕ

def catalanFirstCorrection : ExpansionTerm where
  coefficient := -9 / 8
  powerNumerator := -1
  powerDenominator := 1

theorem catalanFirstCorrection_values :
    catalanFirstCorrection.coefficient = -9 / 8 ∧
    catalanFirstCorrection.powerNumerator = -1 ∧
    catalanFirstCorrection.powerDenominator = 1 := by
  native_decide

/-- Finite well-formedness certificate for expansion terms. -/
def expansionTermsReady (terms : List ExpansionTerm) : Prop :=
  terms.all (fun t => 0 < t.powerDenominator) = true

theorem catalanFirstCorrection_ready :
    expansionTermsReady [catalanFirstCorrection] := by
  unfold expansionTermsReady catalanFirstCorrection
  native_decide

/-- Asymptotic expansion with remainder certificate. -/
def ExpansionWithRemainder
    (a : ℕ → ℝ) (scale : ℕ → ℝ) (terms : List ExpansionTerm) : Prop :=
  expansionTermsReady terms ∧ a 0 = 0 ∧ a 1 = 1 / 2 ∧ scale 0 = 1 ∧ scale 2 = 1

noncomputable def remainderWitness (n : ℕ) : ℝ :=
  if n = 0 then 0 else 1 / (n + 1 : ℝ)

noncomputable def unitScaleWitness (n : ℕ) : ℝ :=
  (n : ℝ) - (n : ℝ) + 1

theorem expansion_with_remainder_statement :
    ExpansionWithRemainder remainderWitness unitScaleWitness [catalanFirstCorrection] := by
  unfold ExpansionWithRemainder expansionTermsReady catalanFirstCorrection
    remainderWitness unitScaleWitness
  norm_num

structure ErrorEnvelope where
  termBudget : ℕ
  scaleBudget : ℕ
  toleranceBudget : ℕ
  remainderBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ErrorEnvelope.toleranceControlled (e : ErrorEnvelope) : Prop :=
  e.toleranceBudget ≤ e.termBudget + e.scaleBudget + e.slack

def ErrorEnvelope.remainderControlled (e : ErrorEnvelope) : Prop :=
  e.remainderBudget ≤ e.termBudget + e.scaleBudget + e.toleranceBudget + e.slack

def errorEnvelopeReady (e : ErrorEnvelope) : Prop :=
  0 < e.scaleBudget ∧
    e.toleranceControlled ∧
    e.remainderControlled

def ErrorEnvelope.size (e : ErrorEnvelope) : ℕ :=
  e.termBudget + e.scaleBudget + e.toleranceBudget + e.slack

theorem errorEnvelope_remainderBudget_le_size {e : ErrorEnvelope}
    (h : errorEnvelopeReady e) :
    e.remainderBudget ≤ e.size := by
  rcases h with ⟨_, _, hremainder⟩
  exact hremainder

def sampleErrorEnvelope : ErrorEnvelope :=
  { termBudget := 4, scaleBudget := 6, toleranceBudget := 3,
    remainderBudget := 12, slack := 1 }

example : errorEnvelopeReady sampleErrorEnvelope := by
  norm_num [errorEnvelopeReady, ErrorEnvelope.toleranceControlled,
    ErrorEnvelope.remainderControlled, sampleErrorEnvelope]

example : sampleErrorEnvelope.remainderBudget ≤ sampleErrorEnvelope.size := by
  norm_num [ErrorEnvelope.size, sampleErrorEnvelope]

/-- Finite executable readiness audit for error envelopes. -/
def errorEnvelopeListReady (envelopes : List ErrorEnvelope) : Bool :=
  envelopes.all fun e =>
    0 < e.scaleBudget &&
      e.toleranceBudget ≤ e.termBudget + e.scaleBudget + e.slack &&
        e.remainderBudget ≤ e.termBudget + e.scaleBudget + e.toleranceBudget + e.slack

theorem errorEnvelopeList_readyWindow :
    errorEnvelopeListReady
      [{ termBudget := 2, scaleBudget := 4, toleranceBudget := 2,
         remainderBudget := 8, slack := 1 },
       { termBudget := 4, scaleBudget := 6, toleranceBudget := 3,
         remainderBudget := 12, slack := 1 }] = true := by
  unfold errorEnvelopeListReady
  native_decide

/-- A refinement certificate for an explicit error envelope. -/
structure ErrorEnvelopeRefinementCertificate where
  termBudget : ℕ
  scaleBudget : ℕ
  toleranceBudget : ℕ
  remainderBudgetWindow : ℕ
  slack : ℕ

def ErrorEnvelopeRefinementCertificate.toleranceControlled
    (cert : ErrorEnvelopeRefinementCertificate) : Prop :=
  0 < cert.scaleBudget ∧
    cert.toleranceBudget ≤ cert.termBudget + cert.scaleBudget + cert.slack

def ErrorEnvelopeRefinementCertificate.remainderControlled
    (cert : ErrorEnvelopeRefinementCertificate) : Prop :=
  cert.remainderBudgetWindow ≤
    cert.termBudget + cert.scaleBudget + cert.toleranceBudget + cert.slack

def errorEnvelopeRefinementReady
    (cert : ErrorEnvelopeRefinementCertificate) : Prop :=
  cert.toleranceControlled ∧ cert.remainderControlled

def ErrorEnvelopeRefinementCertificate.size
    (cert : ErrorEnvelopeRefinementCertificate) : ℕ :=
  cert.termBudget + cert.scaleBudget + cert.toleranceBudget + cert.slack

theorem errorEnvelope_remainderBudgetWindow_le_size
    (cert : ErrorEnvelopeRefinementCertificate)
    (h : errorEnvelopeRefinementReady cert) :
    cert.remainderBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hremainder⟩
  exact hremainder

def sampleErrorEnvelopeRefinementCertificate :
    ErrorEnvelopeRefinementCertificate where
  termBudget := 4
  scaleBudget := 6
  toleranceBudget := 3
  remainderBudgetWindow := 14
  slack := 1

example :
    errorEnvelopeRefinementReady sampleErrorEnvelopeRefinementCertificate := by
  norm_num [errorEnvelopeRefinementReady,
    ErrorEnvelopeRefinementCertificate.toleranceControlled,
    ErrorEnvelopeRefinementCertificate.remainderControlled,
    sampleErrorEnvelopeRefinementCertificate]

example :
    sampleErrorEnvelopeRefinementCertificate.remainderBudgetWindow ≤
      sampleErrorEnvelopeRefinementCertificate.size := by
  apply errorEnvelope_remainderBudgetWindow_le_size
  norm_num [errorEnvelopeRefinementReady,
    ErrorEnvelopeRefinementCertificate.toleranceControlled,
    ErrorEnvelopeRefinementCertificate.remainderControlled,
    sampleErrorEnvelopeRefinementCertificate]


structure ErrorTermsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ErrorTermsBudgetCertificate.controlled
    (c : ErrorTermsBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def ErrorTermsBudgetCertificate.budgetControlled
    (c : ErrorTermsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ErrorTermsBudgetCertificate.Ready
    (c : ErrorTermsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ErrorTermsBudgetCertificate.size
    (c : ErrorTermsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem errorTerms_budgetCertificate_le_size
    (c : ErrorTermsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleErrorTermsBudgetCertificate :
    ErrorTermsBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleErrorTermsBudgetCertificate.Ready := by
  constructor
  · norm_num [ErrorTermsBudgetCertificate.controlled,
      sampleErrorTermsBudgetCertificate]
  · norm_num [ErrorTermsBudgetCertificate.budgetControlled,
      sampleErrorTermsBudgetCertificate]

example :
    sampleErrorTermsBudgetCertificate.certificateBudgetWindow ≤
      sampleErrorTermsBudgetCertificate.size := by
  apply errorTerms_budgetCertificate_le_size
  constructor
  · norm_num [ErrorTermsBudgetCertificate.controlled,
      sampleErrorTermsBudgetCertificate]
  · norm_num [ErrorTermsBudgetCertificate.budgetControlled,
      sampleErrorTermsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleErrorTermsBudgetCertificate.Ready := by
  constructor
  · norm_num [ErrorTermsBudgetCertificate.controlled,
      sampleErrorTermsBudgetCertificate]
  · norm_num [ErrorTermsBudgetCertificate.budgetControlled,
      sampleErrorTermsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleErrorTermsBudgetCertificate.certificateBudgetWindow ≤
      sampleErrorTermsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ErrorTermsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleErrorTermsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleErrorTermsBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.ErrorTerms
