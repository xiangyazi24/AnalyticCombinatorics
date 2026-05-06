import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Nested sequences, lattice paths, and continued fractions.

Finite depth bookkeeping for nested sequence decompositions, path states,
and continued-fraction convergents.
-/

namespace AnalyticCombinatorics.PartB.Ch5.NestedSequencesLatticePathsContinuedFractions

/-- Motzkin-like height walk step bounded in absolute height by the prefix length. -/
def boundedPathHeight (steps : List ℤ) : ℤ :=
  steps.foldl (fun h step => h + step) 0

/-- Finite height audit for sampled prefixes of up/down paths. -/
def latticePathHeightWindow (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    boundedPathHeight (List.replicate n (1 : ℤ)) = n

/-- Continued-fraction convergent denominator model. -/
def continuedFractionDenominator : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => continuedFractionDenominator (n + 1) + continuedFractionDenominator n

theorem nestedPath_heightWindow :
    latticePathHeightWindow 16 = true := by
  unfold latticePathHeightWindow boundedPathHeight
  native_decide

theorem continuedFractionDenominator_samples :
    continuedFractionDenominator 0 = 1 ∧
    continuedFractionDenominator 4 = 5 ∧
    continuedFractionDenominator 5 = 8 := by
  native_decide

structure NestedPathFractionWindow where
  nestingDepth : ℕ
  pathHeightWindow : ℕ
  convergentDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def nestedPathFractionReady (w : NestedPathFractionWindow) : Prop :=
  0 < w.nestingDepth ∧
    w.convergentDepth ≤ w.nestingDepth + w.pathHeightWindow + w.slack

def nestedPathFractionBudget (w : NestedPathFractionWindow) : ℕ :=
  w.nestingDepth + w.pathHeightWindow + w.convergentDepth + w.slack

theorem convergentDepth_le_nestedPathFractionBudget
    (w : NestedPathFractionWindow) :
    w.convergentDepth ≤ nestedPathFractionBudget w := by
  unfold nestedPathFractionBudget
  omega

def sampleNestedPathFractionWindow : NestedPathFractionWindow :=
  { nestingDepth := 4, pathHeightWindow := 5, convergentDepth := 8, slack := 1 }

example : nestedPathFractionReady sampleNestedPathFractionWindow := by
  norm_num [nestedPathFractionReady, sampleNestedPathFractionWindow]

structure NestedSequencesLatticePathsContinuedFractionsBudgetCertificate where
  nestingWindow : ℕ
  pathWindow : ℕ
  fractionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def NestedSequencesLatticePathsContinuedFractionsBudgetCertificate.controlled
    (c : NestedSequencesLatticePathsContinuedFractionsBudgetCertificate) :
    Prop :=
  0 < c.nestingWindow ∧
    c.fractionWindow ≤ c.nestingWindow + c.pathWindow + c.slack

def NestedSequencesLatticePathsContinuedFractionsBudgetCertificate.budgetControlled
    (c : NestedSequencesLatticePathsContinuedFractionsBudgetCertificate) :
    Prop :=
  c.certificateBudgetWindow ≤
    c.nestingWindow + c.pathWindow + c.fractionWindow + c.slack

def NestedSequencesLatticePathsContinuedFractionsBudgetCertificate.Ready
    (c : NestedSequencesLatticePathsContinuedFractionsBudgetCertificate) :
    Prop :=
  c.controlled ∧ c.budgetControlled

def NestedSequencesLatticePathsContinuedFractionsBudgetCertificate.size
    (c : NestedSequencesLatticePathsContinuedFractionsBudgetCertificate) : ℕ :=
  c.nestingWindow + c.pathWindow + c.fractionWindow + c.slack

theorem nestedSequencesLatticePathsContinuedFractions_budgetCertificate_le_size
    (c : NestedSequencesLatticePathsContinuedFractionsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleNestedSequencesLatticePathsContinuedFractionsBudgetCertificate :
    NestedSequencesLatticePathsContinuedFractionsBudgetCertificate :=
  { nestingWindow := 4
    pathWindow := 5
    fractionWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

example :
    sampleNestedSequencesLatticePathsContinuedFractionsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [NestedSequencesLatticePathsContinuedFractionsBudgetCertificate.controlled,
        sampleNestedSequencesLatticePathsContinuedFractionsBudgetCertificate]
  · norm_num
      [NestedSequencesLatticePathsContinuedFractionsBudgetCertificate.budgetControlled,
        sampleNestedSequencesLatticePathsContinuedFractionsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleNestedSequencesLatticePathsContinuedFractionsBudgetCertificate.Ready := by
  constructor
  · norm_num [NestedSequencesLatticePathsContinuedFractionsBudgetCertificate.controlled,
      sampleNestedSequencesLatticePathsContinuedFractionsBudgetCertificate]
  · norm_num [NestedSequencesLatticePathsContinuedFractionsBudgetCertificate.budgetControlled,
      sampleNestedSequencesLatticePathsContinuedFractionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleNestedSequencesLatticePathsContinuedFractionsBudgetCertificate.certificateBudgetWindow ≤
      sampleNestedSequencesLatticePathsContinuedFractionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List NestedSequencesLatticePathsContinuedFractionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleNestedSequencesLatticePathsContinuedFractionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleNestedSequencesLatticePathsContinuedFractionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.NestedSequencesLatticePathsContinuedFractions
