import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# A roadmap to singularity analysis asymptotics
-/

namespace AnalyticCombinatorics.PartB.Ch7.RoadmapToSingularityAnalysisAsymptotics

/-- A finite checklist for the singularity-analysis roadmap. -/
structure SingularityRoadmapChecklist where
  locateSingularities : Bool
  computeExpansion : Bool
  applyTransfer : Bool
deriving DecidableEq, Repr

def SingularityRoadmapChecklist.complete
    (c : SingularityRoadmapChecklist) : Bool :=
  c.locateSingularities && c.computeExpansion && c.applyTransfer

theorem singularityRoadmapChecklist_sample :
    ({ locateSingularities := true, computeExpansion := true,
       applyTransfer := true } : SingularityRoadmapChecklist).complete =
      true := by
  native_decide

/-- Transfer-stage budget after local expansion. -/
def roadmapTransferBudget (locate expansion slack : ℕ) : ℕ :=
  locate + expansion + slack

theorem roadmapTransferBudget_sample :
    roadmapTransferBudget 4 5 1 = 10 := by
  native_decide

structure RoadmapWindow where
  locateWindow : ℕ
  expansionWindow : ℕ
  transferWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RoadmapWindow.ready (w : RoadmapWindow) : Prop :=
  0 < w.locateWindow ∧
    w.transferWindow ≤ w.locateWindow + w.expansionWindow + w.slack

def sampleRoadmapWindow : RoadmapWindow :=
  { locateWindow := 4, expansionWindow := 5, transferWindow := 10, slack := 1 }

example : sampleRoadmapWindow.ready := by
  norm_num [RoadmapWindow.ready, sampleRoadmapWindow]

structure BudgetCertificate where
  locateWindow : ℕ
  expansionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.locateWindow ∧ c.expansionWindow ≤ c.locateWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.locateWindow + c.expansionWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.locateWindow + c.expansionWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { locateWindow := 5, expansionWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  have h : sampleBudgetCertificate.Ready := by
    constructor
    · norm_num [BudgetCertificate.controlled,
        sampleBudgetCertificate]
    · norm_num [BudgetCertificate.budgetControlled,
        sampleBudgetCertificate]
  exact h.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.RoadmapToSingularityAnalysisAsymptotics
