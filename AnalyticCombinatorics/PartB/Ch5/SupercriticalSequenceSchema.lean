import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
The supercritical sequence schema.

Finite dominance-window bookkeeping for sequence constructions whose
denominator singularity precedes component singularities.
-/

namespace AnalyticCombinatorics.PartB.Ch5.SupercriticalSequenceSchema

/-- Coefficients of the sequence schema `1 / (1 - base*z)`. -/
def sequenceSchemaCoeff (base n : ℕ) : ℕ :=
  base ^ n

/-- Finite dominance check: sequence pole coefficients dominate components. -/
def supercriticalDominanceCheck
    (component : ℕ → ℕ) (base N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => component n ≤ sequenceSchemaCoeff base n

theorem supercriticalDominance_geometric :
    supercriticalDominanceCheck (fun n => 2 ^ n) 3 16 = true := by
  unfold supercriticalDominanceCheck sequenceSchemaCoeff
  native_decide

structure SupercriticalSequenceWindow where
  componentRadiusWindow : ℕ
  sequencePoleWindow : ℕ
  dominanceSlack : ℕ
  coefficientDepth : ℕ
deriving DecidableEq, Repr

def supercriticalSequenceReady (w : SupercriticalSequenceWindow) : Prop :=
  0 < w.sequencePoleWindow ∧
    w.coefficientDepth ≤
      w.componentRadiusWindow + w.sequencePoleWindow + w.dominanceSlack

def supercriticalSequenceBudget (w : SupercriticalSequenceWindow) : ℕ :=
  w.componentRadiusWindow + w.sequencePoleWindow +
    w.dominanceSlack + w.coefficientDepth

theorem coefficientDepth_le_supercriticalBudget
    (w : SupercriticalSequenceWindow) :
    w.coefficientDepth ≤ supercriticalSequenceBudget w := by
  unfold supercriticalSequenceBudget
  omega

def sampleSupercriticalSequenceWindow : SupercriticalSequenceWindow :=
  { componentRadiusWindow := 5
    sequencePoleWindow := 3
    dominanceSlack := 2
    coefficientDepth := 8 }

example : supercriticalSequenceReady sampleSupercriticalSequenceWindow := by
  norm_num [supercriticalSequenceReady, sampleSupercriticalSequenceWindow]

structure SupercriticalSequenceSchemaBudgetCertificate where
  componentWindow : ℕ
  poleWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SupercriticalSequenceSchemaBudgetCertificate.controlled
    (c : SupercriticalSequenceSchemaBudgetCertificate) : Prop :=
  0 < c.poleWindow ∧
    c.coefficientWindow ≤ c.componentWindow + c.poleWindow + c.slack

def SupercriticalSequenceSchemaBudgetCertificate.budgetControlled
    (c : SupercriticalSequenceSchemaBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.componentWindow + c.poleWindow + c.coefficientWindow + c.slack

def SupercriticalSequenceSchemaBudgetCertificate.Ready
    (c : SupercriticalSequenceSchemaBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SupercriticalSequenceSchemaBudgetCertificate.size
    (c : SupercriticalSequenceSchemaBudgetCertificate) : ℕ :=
  c.componentWindow + c.poleWindow + c.coefficientWindow + c.slack

theorem supercriticalSequenceSchema_budgetCertificate_le_size
    (c : SupercriticalSequenceSchemaBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSupercriticalSequenceSchemaBudgetCertificate :
    SupercriticalSequenceSchemaBudgetCertificate :=
  { componentWindow := 5
    poleWindow := 3
    coefficientWindow := 8
    certificateBudgetWindow := 18
    slack := 2 }

theorem sampleBudgetCertificate_ready :
    sampleSupercriticalSequenceSchemaBudgetCertificate.Ready := by
  constructor
  · norm_num [SupercriticalSequenceSchemaBudgetCertificate.controlled,
      sampleSupercriticalSequenceSchemaBudgetCertificate]
  · norm_num [SupercriticalSequenceSchemaBudgetCertificate.budgetControlled,
      sampleSupercriticalSequenceSchemaBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSupercriticalSequenceSchemaBudgetCertificate.certificateBudgetWindow ≤
      sampleSupercriticalSequenceSchemaBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSupercriticalSequenceSchemaBudgetCertificate.Ready := by
  constructor
  · norm_num [SupercriticalSequenceSchemaBudgetCertificate.controlled,
      sampleSupercriticalSequenceSchemaBudgetCertificate]
  · norm_num [SupercriticalSequenceSchemaBudgetCertificate.budgetControlled,
      sampleSupercriticalSequenceSchemaBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SupercriticalSequenceSchemaBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSupercriticalSequenceSchemaBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSupercriticalSequenceSchemaBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.SupercriticalSequenceSchema
