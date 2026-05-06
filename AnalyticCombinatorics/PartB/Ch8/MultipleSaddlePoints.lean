import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multiple saddle points.
-/

namespace AnalyticCombinatorics.PartB.Ch8.MultipleSaddlePoints

/-- Integer-valued saddle descriptor for finite interaction checks. -/
structure SaddleDescriptor where
  position : ℤ
  weight : ℕ
deriving DecidableEq, Repr

def separated (a b : SaddleDescriptor) (gap : ℕ) : Prop :=
  (gap : ℤ) ≤ a.position - b.position ∨ (gap : ℤ) ≤ b.position - a.position

/-- Boolean form of saddle separation for executable audits. -/
def separatedBool (a b : SaddleDescriptor) (gap : ℕ) : Bool :=
  decide ((gap : ℤ) ≤ a.position - b.position) ||
    decide ((gap : ℤ) ≤ b.position - a.position)

/-- Finite check that two sampled saddle families stay separated. -/
def pairwiseSeparatedCheck
    (left right : ℕ → SaddleDescriptor) (gap N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => separatedBool (left n) (right n) gap

def leftSaddle (n : ℕ) : SaddleDescriptor :=
  { position := -((n + 2 : ℕ) : ℤ), weight := 1 }

def rightSaddle (n : ℕ) : SaddleDescriptor :=
  { position := (n + 2 : ℕ), weight := 1 }

def MultipleSaddleWindow (N : ℕ) : Prop :=
  pairwiseSeparatedCheck leftSaddle rightSaddle 2 N = true

theorem symmetricSaddles_separated :
    MultipleSaddleWindow 16 := by
  unfold MultipleSaddleWindow pairwiseSeparatedCheck separatedBool
    leftSaddle rightSaddle
  native_decide

/-- Finite audit that sampled saddle weights are positive. -/
def saddleWeightsPositiveCheck (saddles : ℕ → SaddleDescriptor) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => 0 < (saddles n).weight

theorem symmetricSaddles_weightWindow :
    saddleWeightsPositiveCheck leftSaddle 16 = true ∧
      saddleWeightsPositiveCheck rightSaddle 16 = true := by
  unfold saddleWeightsPositiveCheck leftSaddle rightSaddle
  native_decide

example : separatedBool (leftSaddle 2) (rightSaddle 2) 2 = true := by
  unfold separatedBool leftSaddle rightSaddle
  native_decide

example :
    pairwiseSeparatedCheck leftSaddle rightSaddle 2 6 = true := by
  unfold pairwiseSeparatedCheck separatedBool leftSaddle rightSaddle
  native_decide

structure MultipleSaddlePointsBudgetCertificate where
  saddleCountWindow : ℕ
  interactionWindow : ℕ
  uniformityWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultipleSaddlePointsBudgetCertificate.controlled
    (c : MultipleSaddlePointsBudgetCertificate) : Prop :=
  0 < c.saddleCountWindow ∧
    c.uniformityWindow ≤ c.saddleCountWindow + c.interactionWindow + c.slack

def MultipleSaddlePointsBudgetCertificate.budgetControlled
    (c : MultipleSaddlePointsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleCountWindow + c.interactionWindow + c.uniformityWindow + c.slack

def MultipleSaddlePointsBudgetCertificate.Ready
    (c : MultipleSaddlePointsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultipleSaddlePointsBudgetCertificate.size
    (c : MultipleSaddlePointsBudgetCertificate) : ℕ :=
  c.saddleCountWindow + c.interactionWindow + c.uniformityWindow + c.slack

theorem multipleSaddlePoints_budgetCertificate_le_size
    (c : MultipleSaddlePointsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleMultipleSaddlePointsBudgetCertificate :
    MultipleSaddlePointsBudgetCertificate :=
  { saddleCountWindow := 4
    interactionWindow := 6
    uniformityWindow := 9
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMultipleSaddlePointsBudgetCertificate.Ready := by
  constructor
  · norm_num [MultipleSaddlePointsBudgetCertificate.controlled,
      sampleMultipleSaddlePointsBudgetCertificate]
  · norm_num [MultipleSaddlePointsBudgetCertificate.budgetControlled,
      sampleMultipleSaddlePointsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultipleSaddlePointsBudgetCertificate.certificateBudgetWindow ≤
      sampleMultipleSaddlePointsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMultipleSaddlePointsBudgetCertificate.Ready := by
  constructor
  · norm_num [MultipleSaddlePointsBudgetCertificate.controlled,
      sampleMultipleSaddlePointsBudgetCertificate]
  · norm_num [MultipleSaddlePointsBudgetCertificate.budgetControlled,
      sampleMultipleSaddlePointsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MultipleSaddlePointsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleMultipleSaddlePointsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleMultipleSaddlePointsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.MultipleSaddlePoints
