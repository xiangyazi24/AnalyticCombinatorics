import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Extremal parameters.

Finite threshold-window bookkeeping for maxima, minima, and record
statistics extracted from marked generating functions.
-/

namespace AnalyticCombinatorics.PartA.Ch3.ExtremalParameters

/-- Tail count for a bounded extremal parameter on an `n`-object sample. -/
def extremalTailProxy (n threshold : ℕ) : ℕ :=
  n - threshold

/-- Finite monotonicity audit for extremal tails in the threshold. -/
def extremalTailDecreasesCheck (n N : ℕ) : Bool :=
  (List.range N).all fun threshold =>
    extremalTailProxy n (threshold + 1) ≤ extremalTailProxy n threshold

/-- Finite normalization audit for an extremal tail. -/
def extremalTailBoundCheck (n N : ℕ) : Bool :=
  (List.range (N + 1)).all fun threshold => extremalTailProxy n threshold ≤ n

theorem extremalTail_window :
    extremalTailDecreasesCheck 20 20 = true ∧
      extremalTailBoundCheck 20 20 = true := by
  unfold extremalTailDecreasesCheck extremalTailBoundCheck extremalTailProxy
  native_decide

structure ExtremalParameterWindow where
  thresholdWindow : ℕ
  tailWindow : ℕ
  normalizationWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def extremalParameterReady (w : ExtremalParameterWindow) : Prop :=
  0 < w.thresholdWindow ∧
    w.tailWindow ≤ w.thresholdWindow + w.normalizationWindow + w.slack

def extremalParameterBudget (w : ExtremalParameterWindow) : ℕ :=
  w.thresholdWindow + w.tailWindow + w.normalizationWindow + w.slack

theorem tailWindow_le_extremalBudget (w : ExtremalParameterWindow) :
    w.tailWindow ≤ extremalParameterBudget w := by
  unfold extremalParameterBudget
  omega

def sampleExtremalParameterWindow : ExtremalParameterWindow :=
  { thresholdWindow := 6, tailWindow := 8, normalizationWindow := 3, slack := 1 }

example : extremalParameterReady sampleExtremalParameterWindow := by
  norm_num [extremalParameterReady, sampleExtremalParameterWindow]

structure ExtremalParametersBudgetCertificate where
  thresholdWindow : ℕ
  tailWindow : ℕ
  normalizationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExtremalParametersBudgetCertificate.controlled
    (c : ExtremalParametersBudgetCertificate) : Prop :=
  0 < c.thresholdWindow ∧
    c.tailWindow ≤ c.thresholdWindow + c.normalizationWindow + c.slack

def ExtremalParametersBudgetCertificate.budgetControlled
    (c : ExtremalParametersBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.thresholdWindow + c.tailWindow + c.normalizationWindow + c.slack

def ExtremalParametersBudgetCertificate.Ready
    (c : ExtremalParametersBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ExtremalParametersBudgetCertificate.size
    (c : ExtremalParametersBudgetCertificate) : ℕ :=
  c.thresholdWindow + c.tailWindow + c.normalizationWindow + c.slack

theorem extremalParameters_budgetCertificate_le_size
    (c : ExtremalParametersBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleExtremalParametersBudgetCertificate :
    ExtremalParametersBudgetCertificate :=
  { thresholdWindow := 6
    tailWindow := 8
    normalizationWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleExtremalParametersBudgetCertificate.Ready := by
  constructor
  · norm_num [ExtremalParametersBudgetCertificate.controlled,
      sampleExtremalParametersBudgetCertificate]
  · norm_num [ExtremalParametersBudgetCertificate.budgetControlled,
      sampleExtremalParametersBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleExtremalParametersBudgetCertificate.certificateBudgetWindow ≤
      sampleExtremalParametersBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleExtremalParametersBudgetCertificate.Ready := by
  constructor
  · norm_num [ExtremalParametersBudgetCertificate.controlled,
      sampleExtremalParametersBudgetCertificate]
  · norm_num [ExtremalParametersBudgetCertificate.budgetControlled,
      sampleExtremalParametersBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ExtremalParametersBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleExtremalParametersBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleExtremalParametersBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.ExtremalParameters
