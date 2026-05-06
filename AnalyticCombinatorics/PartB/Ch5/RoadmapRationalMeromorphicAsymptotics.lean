import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Roadmap to rational and meromorphic asymptotics.

Finite bookkeeping for the pipeline from singularity localization to
coefficient extraction.
-/

namespace AnalyticCombinatorics.PartB.Ch5.RoadmapRationalMeromorphicAsymptotics

/-- Finite state for the rational/meromorphic asymptotic pipeline. -/
structure MeromorphicRoadmapState where
  localizedSingularities : Bool
  extractedPole : Bool
  transferredCoefficients : Bool
deriving DecidableEq, Repr

def MeromorphicRoadmapState.complete (s : MeromorphicRoadmapState) : Bool :=
  s.localizedSingularities && s.extractedPole && s.transferredCoefficients

/-- Coefficient output of a completed simple-pole roadmap. -/
def roadmapSimplePoleCoeff (complete : Bool) (base n : ℕ) : ℕ :=
  if complete then base ^ n else 0

def roadmapCoefficientEnvelopeCheck
    (s : MeromorphicRoadmapState) (base N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    roadmapSimplePoleCoeff s.complete base n ≤ base ^ n

theorem completeRoadmap_envelope :
    roadmapCoefficientEnvelopeCheck
      { localizedSingularities := true
        extractedPole := true
        transferredCoefficients := true } 3 16 = true := by
  unfold roadmapCoefficientEnvelopeCheck roadmapSimplePoleCoeff
    MeromorphicRoadmapState.complete
  native_decide

structure RationalMeromorphicRoadmapWindow where
  singularityWindow : ℕ
  poleOrderWindow : ℕ
  coefficientWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def roadmapReady (w : RationalMeromorphicRoadmapWindow) : Prop :=
  0 < w.singularityWindow ∧
    w.poleOrderWindow ≤ w.singularityWindow + w.coefficientWindow + w.slack

def roadmapBudget (w : RationalMeromorphicRoadmapWindow) : ℕ :=
  w.singularityWindow + w.poleOrderWindow + w.coefficientWindow + w.slack

theorem poleOrderWindow_le_roadmapBudget
    (w : RationalMeromorphicRoadmapWindow) :
    w.poleOrderWindow ≤ roadmapBudget w := by
  unfold roadmapBudget
  omega

def sampleRationalMeromorphicRoadmapWindow :
    RationalMeromorphicRoadmapWindow :=
  { singularityWindow := 5
    poleOrderWindow := 4
    coefficientWindow := 6
    slack := 1 }

example : roadmapReady sampleRationalMeromorphicRoadmapWindow := by
  norm_num [roadmapReady, sampleRationalMeromorphicRoadmapWindow]

structure RoadmapRationalMeromorphicAsymptoticsBudgetCertificate where
  singularityWindow : ℕ
  poleWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RoadmapRationalMeromorphicAsymptoticsBudgetCertificate.controlled
    (c : RoadmapRationalMeromorphicAsymptoticsBudgetCertificate) : Prop :=
  0 < c.singularityWindow ∧
    c.poleWindow ≤ c.singularityWindow + c.coefficientWindow + c.slack

def RoadmapRationalMeromorphicAsymptoticsBudgetCertificate.budgetControlled
    (c : RoadmapRationalMeromorphicAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.singularityWindow + c.poleWindow + c.coefficientWindow + c.slack

def RoadmapRationalMeromorphicAsymptoticsBudgetCertificate.Ready
    (c : RoadmapRationalMeromorphicAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RoadmapRationalMeromorphicAsymptoticsBudgetCertificate.size
    (c : RoadmapRationalMeromorphicAsymptoticsBudgetCertificate) : ℕ :=
  c.singularityWindow + c.poleWindow + c.coefficientWindow + c.slack

theorem roadmapRationalMeromorphicAsymptotics_budgetCertificate_le_size
    (c : RoadmapRationalMeromorphicAsymptoticsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleRoadmapRationalMeromorphicAsymptoticsBudgetCertificate :
    RoadmapRationalMeromorphicAsymptoticsBudgetCertificate :=
  { singularityWindow := 5
    poleWindow := 4
    coefficientWindow := 6
    certificateBudgetWindow := 16
    slack := 1 }

example :
    sampleRoadmapRationalMeromorphicAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [RoadmapRationalMeromorphicAsymptoticsBudgetCertificate.controlled,
        sampleRoadmapRationalMeromorphicAsymptoticsBudgetCertificate]
  · norm_num
      [RoadmapRationalMeromorphicAsymptoticsBudgetCertificate.budgetControlled,
        sampleRoadmapRationalMeromorphicAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleRoadmapRationalMeromorphicAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [RoadmapRationalMeromorphicAsymptoticsBudgetCertificate.controlled,
      sampleRoadmapRationalMeromorphicAsymptoticsBudgetCertificate]
  · norm_num [RoadmapRationalMeromorphicAsymptoticsBudgetCertificate.budgetControlled,
      sampleRoadmapRationalMeromorphicAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRoadmapRationalMeromorphicAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleRoadmapRationalMeromorphicAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RoadmapRationalMeromorphicAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRoadmapRationalMeromorphicAsymptoticsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleRoadmapRationalMeromorphicAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.RoadmapRationalMeromorphicAsymptotics
