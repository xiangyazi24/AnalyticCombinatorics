import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Airy transition windows.

This module records finite bookkeeping for uniform Airy transition windows.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformAiryTransitionWindows

structure AiryTransitionWindowData where
  transitionScale : ℕ
  airyWindow : ℕ
  transitionSlack : ℕ
deriving DecidableEq, Repr

def hasTransitionScale (d : AiryTransitionWindowData) : Prop :=
  0 < d.transitionScale

def airyWindowControlled (d : AiryTransitionWindowData) : Prop :=
  d.airyWindow ≤ d.transitionScale + d.transitionSlack

def airyTransitionReady (d : AiryTransitionWindowData) : Prop :=
  hasTransitionScale d ∧ airyWindowControlled d

def airyTransitionBudget (d : AiryTransitionWindowData) : ℕ :=
  d.transitionScale + d.airyWindow + d.transitionSlack

theorem airyTransitionReady.hasTransitionScale
    {d : AiryTransitionWindowData}
    (h : airyTransitionReady d) :
    hasTransitionScale d ∧ airyWindowControlled d ∧ d.airyWindow ≤ airyTransitionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold airyTransitionBudget
  omega

theorem airyWindow_le_budget (d : AiryTransitionWindowData) :
    d.airyWindow ≤ airyTransitionBudget d := by
  unfold airyTransitionBudget
  omega

def sampleAiryTransitionWindowData : AiryTransitionWindowData :=
  { transitionScale := 7, airyWindow := 9, transitionSlack := 3 }

example : airyTransitionReady sampleAiryTransitionWindowData := by
  norm_num [airyTransitionReady, hasTransitionScale]
  norm_num [airyWindowControlled, sampleAiryTransitionWindowData]

example : airyTransitionBudget sampleAiryTransitionWindowData = 19 := by
  native_decide

/-- Finite executable readiness audit for Airy transition window data. -/
def airyTransitionDataListReady
    (data : List AiryTransitionWindowData) : Bool :=
  data.all fun d => 0 < d.transitionScale && d.airyWindow ≤ d.transitionScale + d.transitionSlack

theorem airyTransitionDataList_readyWindow :
    airyTransitionDataListReady
      [{ transitionScale := 4, airyWindow := 5, transitionSlack := 1 },
       { transitionScale := 7, airyWindow := 9, transitionSlack := 3 }] = true := by
  unfold airyTransitionDataListReady
  native_decide

structure AiryTransitionCertificateWindow where
  transitionWindow : ℕ
  airyWindow : ℕ
  transitionSlack : ℕ
  airyBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AiryTransitionCertificateWindow.airyControlled
    (w : AiryTransitionCertificateWindow) : Prop :=
  w.airyWindow ≤ w.transitionWindow + w.transitionSlack + w.slack

def airyTransitionCertificateReady
    (w : AiryTransitionCertificateWindow) : Prop :=
  0 < w.transitionWindow ∧ w.airyControlled ∧
    w.airyBudget ≤ w.transitionWindow + w.airyWindow + w.slack

def AiryTransitionCertificateWindow.certificate
    (w : AiryTransitionCertificateWindow) : ℕ :=
  w.transitionWindow + w.airyWindow + w.transitionSlack + w.airyBudget + w.slack

theorem airyTransition_budget_le_certificate
    (w : AiryTransitionCertificateWindow) :
    w.airyBudget ≤ w.certificate := by
  unfold AiryTransitionCertificateWindow.certificate
  omega

def sampleAiryTransitionCertificateWindow :
    AiryTransitionCertificateWindow :=
  { transitionWindow := 6, airyWindow := 8, transitionSlack := 2,
    airyBudget := 15, slack := 1 }

example : airyTransitionCertificateReady sampleAiryTransitionCertificateWindow := by
  norm_num [airyTransitionCertificateReady,
    AiryTransitionCertificateWindow.airyControlled, sampleAiryTransitionCertificateWindow]

/-- A refinement certificate for uniform Airy transition windows. -/
structure AiryTransitionRefinementCertificate where
  transitionWindow : ℕ
  airyWindow : ℕ
  transitionSlackWindow : ℕ
  airyBudgetWindow : ℕ
  slack : ℕ

/-- Airy and transition budgets are controlled by transition scale. -/
def airyTransitionRefinementCertificateControlled
    (w : AiryTransitionRefinementCertificate) : Prop :=
  0 < w.transitionWindow ∧
    w.airyWindow ≤ w.transitionWindow + w.transitionSlackWindow + w.slack ∧
      w.airyBudgetWindow ≤ w.transitionWindow + w.airyWindow + w.slack

/-- Readiness for an Airy transition refinement certificate. -/
def airyTransitionRefinementCertificateReady
    (w : AiryTransitionRefinementCertificate) : Prop :=
  airyTransitionRefinementCertificateControlled w ∧
    w.airyBudgetWindow ≤
      w.transitionWindow + w.airyWindow + w.transitionSlackWindow +
        w.airyBudgetWindow + w.slack

/-- Total size of an Airy transition refinement certificate. -/
def airyTransitionRefinementCertificateSize
    (w : AiryTransitionRefinementCertificate) : ℕ :=
  w.transitionWindow + w.airyWindow + w.transitionSlackWindow +
    w.airyBudgetWindow + w.slack

theorem airyTransitionRefinementCertificate_budget_le_size
    (w : AiryTransitionRefinementCertificate)
    (h : airyTransitionRefinementCertificateReady w) :
    w.airyBudgetWindow ≤ airyTransitionRefinementCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold airyTransitionRefinementCertificateSize
  omega

def sampleAiryTransitionRefinementCertificate :
    AiryTransitionRefinementCertificate where
  transitionWindow := 6
  airyWindow := 8
  transitionSlackWindow := 2
  airyBudgetWindow := 15
  slack := 1

example :
    airyTransitionRefinementCertificateReady
      sampleAiryTransitionRefinementCertificate := by
  norm_num [airyTransitionRefinementCertificateReady,
    airyTransitionRefinementCertificateControlled,
    sampleAiryTransitionRefinementCertificate]

example :
    sampleAiryTransitionRefinementCertificate.airyBudgetWindow ≤
      airyTransitionRefinementCertificateSize
        sampleAiryTransitionRefinementCertificate := by
  apply airyTransitionRefinementCertificate_budget_le_size
  norm_num [airyTransitionRefinementCertificateReady,
    airyTransitionRefinementCertificateControlled,
    sampleAiryTransitionRefinementCertificate]

/-- A second-stage certificate with the Airy-transition budget separated from size. -/
structure AiryTransitionBudgetCertificate where
  transitionWindow : ℕ
  airyWindow : ℕ
  transitionSlackWindow : ℕ
  airyBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AiryTransitionBudgetCertificate.airyControlled
    (cert : AiryTransitionBudgetCertificate) : Prop :=
  0 < cert.transitionWindow ∧
    cert.airyWindow ≤ cert.transitionWindow + cert.transitionSlackWindow + cert.slack ∧
      cert.airyBudgetWindow ≤ cert.transitionWindow + cert.airyWindow + cert.slack

def AiryTransitionBudgetCertificate.budgetControlled
    (cert : AiryTransitionBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.transitionWindow + cert.airyWindow + cert.transitionSlackWindow +
      cert.airyBudgetWindow + cert.slack

def airyTransitionBudgetReady (cert : AiryTransitionBudgetCertificate) : Prop :=
  cert.airyControlled ∧ cert.budgetControlled

def AiryTransitionBudgetCertificate.size
    (cert : AiryTransitionBudgetCertificate) : ℕ :=
  cert.transitionWindow + cert.airyWindow + cert.transitionSlackWindow +
    cert.airyBudgetWindow + cert.slack

theorem airyTransition_certificateBudgetWindow_le_size
    (cert : AiryTransitionBudgetCertificate)
    (h : airyTransitionBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAiryTransitionBudgetCertificate :
    AiryTransitionBudgetCertificate :=
  { transitionWindow := 6, airyWindow := 8, transitionSlackWindow := 2,
    airyBudgetWindow := 15, certificateBudgetWindow := 32, slack := 1 }

example : airyTransitionBudgetReady sampleAiryTransitionBudgetCertificate := by
  norm_num [airyTransitionBudgetReady,
    AiryTransitionBudgetCertificate.airyControlled,
    AiryTransitionBudgetCertificate.budgetControlled,
    sampleAiryTransitionBudgetCertificate]

example :
    sampleAiryTransitionBudgetCertificate.certificateBudgetWindow ≤
      sampleAiryTransitionBudgetCertificate.size := by
  apply airyTransition_certificateBudgetWindow_le_size
  norm_num [airyTransitionBudgetReady,
    AiryTransitionBudgetCertificate.airyControlled,
    AiryTransitionBudgetCertificate.budgetControlled,
    sampleAiryTransitionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    airyTransitionBudgetReady sampleAiryTransitionBudgetCertificate := by
  constructor
  · norm_num [AiryTransitionBudgetCertificate.airyControlled,
      sampleAiryTransitionBudgetCertificate]
  · norm_num [AiryTransitionBudgetCertificate.budgetControlled,
      sampleAiryTransitionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAiryTransitionBudgetCertificate.certificateBudgetWindow ≤
      sampleAiryTransitionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AiryTransitionBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAiryTransitionBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAiryTransitionBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformAiryTransitionWindows
