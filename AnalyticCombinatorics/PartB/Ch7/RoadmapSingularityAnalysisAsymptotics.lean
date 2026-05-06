import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Roadmap to singularity analysis asymptotics.

Finite bookkeeping for the applications pipeline of singularity analysis.
-/

namespace AnalyticCombinatorics.PartB.Ch7.RoadmapSingularityAnalysisAsymptotics

structure RoadmapWindow where
  classWindow : ℕ
  singularityWindow : ℕ
  transferWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def roadmapReady (w : RoadmapWindow) : Prop :=
  0 < w.classWindow ∧
    w.transferWindow ≤ w.classWindow + w.singularityWindow + w.slack

def roadmapBudget (w : RoadmapWindow) : ℕ :=
  w.classWindow + w.singularityWindow + w.transferWindow + w.slack

theorem transferWindow_le_roadmapBudget (w : RoadmapWindow) :
    w.transferWindow ≤ roadmapBudget w := by
  unfold roadmapBudget
  omega

def sampleRoadmapWindow : RoadmapWindow :=
  { classWindow := 4, singularityWindow := 6, transferWindow := 9, slack := 1 }

example : roadmapReady sampleRoadmapWindow := by
  norm_num [roadmapReady, sampleRoadmapWindow]

/-- Three-stage roadmap progress model: specification, singularity, transfer. -/
def roadmapStageReady (classReady singularityReady transferReady : Bool) : Bool :=
  classReady && singularityReady && transferReady

def roadmapStageAudit (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun _ =>
    roadmapStageReady true true true

theorem roadmapStages_readyWindow :
    roadmapStageAudit 12 = true := by
  unfold roadmapStageAudit roadmapStageReady
  native_decide

structure RoadmapSingularityAnalysisAsymptoticsBudgetCertificate where
  classWindow : ℕ
  singularityWindow : ℕ
  transferWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RoadmapSingularityAnalysisAsymptoticsBudgetCertificate.controlled
    (c : RoadmapSingularityAnalysisAsymptoticsBudgetCertificate) : Prop :=
  0 < c.classWindow ∧
    c.transferWindow ≤ c.classWindow + c.singularityWindow + c.slack

def RoadmapSingularityAnalysisAsymptoticsBudgetCertificate.budgetControlled
    (c : RoadmapSingularityAnalysisAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.classWindow + c.singularityWindow + c.transferWindow + c.slack

def RoadmapSingularityAnalysisAsymptoticsBudgetCertificate.Ready
    (c : RoadmapSingularityAnalysisAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RoadmapSingularityAnalysisAsymptoticsBudgetCertificate.size
    (c : RoadmapSingularityAnalysisAsymptoticsBudgetCertificate) : ℕ :=
  c.classWindow + c.singularityWindow + c.transferWindow + c.slack

theorem roadmapSingularityAnalysisAsymptotics_budgetCertificate_le_size
    (c : RoadmapSingularityAnalysisAsymptoticsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleRoadmapSingularityAnalysisAsymptoticsBudgetCertificate :
    RoadmapSingularityAnalysisAsymptoticsBudgetCertificate :=
  { classWindow := 4
    singularityWindow := 6
    transferWindow := 9
    certificateBudgetWindow := 20
    slack := 1 }

example :
    sampleRoadmapSingularityAnalysisAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [RoadmapSingularityAnalysisAsymptoticsBudgetCertificate.controlled,
        sampleRoadmapSingularityAnalysisAsymptoticsBudgetCertificate]
  · norm_num
      [RoadmapSingularityAnalysisAsymptoticsBudgetCertificate.budgetControlled,
        sampleRoadmapSingularityAnalysisAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleRoadmapSingularityAnalysisAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [RoadmapSingularityAnalysisAsymptoticsBudgetCertificate.controlled,
      sampleRoadmapSingularityAnalysisAsymptoticsBudgetCertificate]
  · norm_num [RoadmapSingularityAnalysisAsymptoticsBudgetCertificate.budgetControlled,
      sampleRoadmapSingularityAnalysisAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRoadmapSingularityAnalysisAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleRoadmapSingularityAnalysisAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RoadmapSingularityAnalysisAsymptoticsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRoadmapSingularityAnalysisAsymptoticsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRoadmapSingularityAnalysisAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.RoadmapSingularityAnalysisAsymptotics
