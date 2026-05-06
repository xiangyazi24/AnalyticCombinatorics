import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# A glimpse of basic singularity analysis theory
-/

namespace AnalyticCombinatorics.PartB.Ch6.GlimpseOfBasicSingularityAnalysisTheory

/-- Local singular term with an exponent numerator and denominator. -/
structure LocalSingularTerm where
  coefficient : ℕ
  exponentNumerator : ℕ
  exponentDenominator : ℕ
deriving DecidableEq, Repr

def LocalSingularTerm.valid (t : LocalSingularTerm) : Prop :=
  0 < t.exponentDenominator

theorem localSingularTerm_sample_valid :
    ({ coefficient := 3, exponentNumerator := 1,
       exponentDenominator := 2 } : LocalSingularTerm).valid := by
  norm_num [LocalSingularTerm.valid]

/-- Toy transfer envelope for a local singular term. -/
def transferEnvelope (termSize n : ℕ) : ℕ :=
  termSize * (n + 1)

theorem transferEnvelope_monotone_sample :
    transferEnvelope 3 4 ≤ transferEnvelope 3 5 := by
  native_decide

structure BasicSingularityTheoryWindow where
  localExpansionWindow : ℕ
  deltaDomainWindow : ℕ
  transferWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BasicSingularityTheoryWindow.ready
    (w : BasicSingularityTheoryWindow) : Prop :=
  0 < w.localExpansionWindow ∧
    w.transferWindow ≤ w.localExpansionWindow + w.deltaDomainWindow + w.slack

def sampleBasicSingularityTheoryWindow : BasicSingularityTheoryWindow :=
  { localExpansionWindow := 3
    deltaDomainWindow := 4
    transferWindow := 7
    slack := 0 }

example : sampleBasicSingularityTheoryWindow.ready := by
  norm_num [BasicSingularityTheoryWindow.ready,
    sampleBasicSingularityTheoryWindow]

structure GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate where
  localWindow : ℕ
  domainWindow : ℕ
  transferWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.controlled
    (c : GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate) : Prop :=
  0 < c.localWindow ∧
    c.transferWindow ≤ c.localWindow + c.domainWindow + c.slack

def GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.budgetControlled
    (c : GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.localWindow + c.domainWindow + c.transferWindow + c.slack

def GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.Ready
    (c : GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.size
    (c : GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate) : ℕ :=
  c.localWindow + c.domainWindow + c.transferWindow + c.slack

def sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate :
    GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate :=
  { localWindow := 3
    domainWindow := 4
    transferWindow := 7
    certificateBudgetWindow := 15
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.controlled,
      sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate]
  · norm_num [GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.budgetControlled,
      sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num
      [GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.controlled,
        sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate]
  · norm_num
      [GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.budgetControlled,
        sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate]

def budgetCertificateListReady
    (data : List GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate_ready :
    sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num
      [GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.controlled,
        sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate]
  · norm_num
      [GlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate.budgetControlled,
        sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate] =
        true := by
  unfold budgetCertificateListReady
    sampleGlimpseOfBasicSingularityAnalysisTheoryBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.GlimpseOfBasicSingularityAnalysisTheory
