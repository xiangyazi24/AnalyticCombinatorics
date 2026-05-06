import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Preface

Finite roadmap bookkeeping for the prefatory scope of the formalization.
-/

namespace AnalyticCombinatorics.Preface

/-- Preface coverage score across symbolic, analytic, and probabilistic themes. -/
def prefaceCoverageScore (symbolic analytic probability : ℕ) : ℕ :=
  symbolic + analytic + probability

theorem prefaceCoverageScore_sample :
    prefaceCoverageScore 4 5 10 = 19 := by
  native_decide

/-- Whether the preface roadmap has enough analytic support for random models. -/
def prefaceRoadmapBalanced
    (symbolic analytic random slack : ℕ) : Bool :=
  random ≤ symbolic + analytic + slack

theorem prefaceRoadmapBalanced_sample :
    prefaceRoadmapBalanced 4 5 10 1 = true := by
  native_decide

structure ScopeWindow where
  symbolicWindow : ℕ
  analyticWindow : ℕ
  randomStructureWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ScopeWindow.ready (w : ScopeWindow) : Prop :=
  0 < w.symbolicWindow ∧
    w.randomStructureWindow ≤ w.symbolicWindow + w.analyticWindow + w.slack

def sampleScopeWindow : ScopeWindow :=
  { symbolicWindow := 4, analyticWindow := 5,
    randomStructureWindow := 10, slack := 1 }

example : sampleScopeWindow.ready := by
  norm_num [ScopeWindow.ready, sampleScopeWindow]

structure BudgetCertificate where
  scopeWindow : ℕ
  roadmapWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.scopeWindow ∧ c.roadmapWindow ≤ c.scopeWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.scopeWindow + c.roadmapWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.scopeWindow + c.roadmapWindow + c.slack

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { scopeWindow := 5, roadmapWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  norm_num [BudgetCertificate.size, sampleBudgetCertificate]

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

end AnalyticCombinatorics.Preface
