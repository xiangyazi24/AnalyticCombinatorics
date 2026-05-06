import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Watson lemma windows.

This module records finite bookkeeping for Watson lemma remainder windows.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformWatsonLemmaWindows

structure WatsonLemmaWindowData where
  expansionOrder : ℕ
  laplaceWindow : ℕ
  watsonSlack : ℕ
deriving DecidableEq, Repr

def hasExpansionOrder (d : WatsonLemmaWindowData) : Prop :=
  0 < d.expansionOrder

def laplaceWindowControlled (d : WatsonLemmaWindowData) : Prop :=
  d.laplaceWindow ≤ d.expansionOrder + d.watsonSlack

def watsonLemmaReady (d : WatsonLemmaWindowData) : Prop :=
  hasExpansionOrder d ∧ laplaceWindowControlled d

def watsonLemmaBudget (d : WatsonLemmaWindowData) : ℕ :=
  d.expansionOrder + d.laplaceWindow + d.watsonSlack

theorem watsonLemmaReady.hasExpansionOrder
    {d : WatsonLemmaWindowData}
    (h : watsonLemmaReady d) :
    hasExpansionOrder d ∧ laplaceWindowControlled d ∧
      d.laplaceWindow ≤ watsonLemmaBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold watsonLemmaBudget
  omega

theorem laplaceWindow_le_budget (d : WatsonLemmaWindowData) :
    d.laplaceWindow ≤ watsonLemmaBudget d := by
  unfold watsonLemmaBudget
  omega

def sampleWatsonLemmaWindowData : WatsonLemmaWindowData :=
  { expansionOrder := 6, laplaceWindow := 8, watsonSlack := 3 }

example : watsonLemmaReady sampleWatsonLemmaWindowData := by
  norm_num [watsonLemmaReady, hasExpansionOrder]
  norm_num [laplaceWindowControlled, sampleWatsonLemmaWindowData]

example : watsonLemmaBudget sampleWatsonLemmaWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for Watson lemma windows. -/
def watsonLemmaWindowDataListReady
    (data : List WatsonLemmaWindowData) : Bool :=
  data.all fun d =>
    0 < d.expansionOrder && d.laplaceWindow ≤ d.expansionOrder + d.watsonSlack

theorem watsonLemmaWindowDataList_readyWindow :
    watsonLemmaWindowDataListReady
      [{ expansionOrder := 4, laplaceWindow := 5, watsonSlack := 1 },
       { expansionOrder := 6, laplaceWindow := 8, watsonSlack := 3 }] = true := by
  unfold watsonLemmaWindowDataListReady
  native_decide

/-- A certificate window for uniform Watson lemma estimates. -/
structure WatsonLemmaCertificateWindow where
  expansionWindow : ℕ
  laplaceWindow : ℕ
  watsonSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The Laplace window is controlled by expansion order and slack. -/
def watsonLemmaCertificateControlled
    (w : WatsonLemmaCertificateWindow) : Prop :=
  w.laplaceWindow ≤ w.expansionWindow + w.watsonSlack + w.slack

/-- Readiness for a Watson lemma certificate. -/
def watsonLemmaCertificateReady
    (w : WatsonLemmaCertificateWindow) : Prop :=
  0 < w.expansionWindow ∧
    watsonLemmaCertificateControlled w ∧
      w.certificateBudget ≤ w.expansionWindow + w.laplaceWindow + w.slack

/-- Total size of a Watson lemma certificate. -/
def watsonLemmaCertificate (w : WatsonLemmaCertificateWindow) : ℕ :=
  w.expansionWindow + w.laplaceWindow + w.watsonSlack + w.certificateBudget + w.slack

theorem watsonLemmaCertificate_budget_le_certificate
    (w : WatsonLemmaCertificateWindow)
    (h : watsonLemmaCertificateReady w) :
    w.certificateBudget ≤ watsonLemmaCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold watsonLemmaCertificate
  omega

def sampleWatsonLemmaCertificateWindow :
    WatsonLemmaCertificateWindow where
  expansionWindow := 6
  laplaceWindow := 7
  watsonSlack := 2
  certificateBudget := 12
  slack := 1

example :
    watsonLemmaCertificateReady sampleWatsonLemmaCertificateWindow := by
  norm_num [watsonLemmaCertificateReady,
    watsonLemmaCertificateControlled, sampleWatsonLemmaCertificateWindow]

example :
    sampleWatsonLemmaCertificateWindow.certificateBudget ≤
      watsonLemmaCertificate sampleWatsonLemmaCertificateWindow := by
  apply watsonLemmaCertificate_budget_le_certificate
  norm_num [watsonLemmaCertificateReady,
    watsonLemmaCertificateControlled, sampleWatsonLemmaCertificateWindow]

structure WatsonLemmaRefinementCertificate where
  expansionWindow : ℕ
  laplaceWindow : ℕ
  watsonSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WatsonLemmaRefinementCertificate.laplaceControlled
    (c : WatsonLemmaRefinementCertificate) : Prop :=
  c.laplaceWindow ≤ c.expansionWindow + c.watsonSlackWindow + c.slack

def WatsonLemmaRefinementCertificate.certificateBudgetControlled
    (c : WatsonLemmaRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.expansionWindow + c.laplaceWindow + c.watsonSlackWindow + c.slack

def watsonLemmaRefinementReady
    (c : WatsonLemmaRefinementCertificate) : Prop :=
  0 < c.expansionWindow ∧ c.laplaceControlled ∧ c.certificateBudgetControlled

def WatsonLemmaRefinementCertificate.size
    (c : WatsonLemmaRefinementCertificate) : ℕ :=
  c.expansionWindow + c.laplaceWindow + c.watsonSlackWindow + c.slack

theorem watsonLemma_certificateBudgetWindow_le_size
    {c : WatsonLemmaRefinementCertificate}
    (h : watsonLemmaRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleWatsonLemmaRefinementCertificate :
    WatsonLemmaRefinementCertificate :=
  { expansionWindow := 6, laplaceWindow := 7, watsonSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : watsonLemmaRefinementReady
    sampleWatsonLemmaRefinementCertificate := by
  norm_num [watsonLemmaRefinementReady,
    WatsonLemmaRefinementCertificate.laplaceControlled,
    WatsonLemmaRefinementCertificate.certificateBudgetControlled,
    sampleWatsonLemmaRefinementCertificate]

example :
    sampleWatsonLemmaRefinementCertificate.certificateBudgetWindow ≤
      sampleWatsonLemmaRefinementCertificate.size := by
  norm_num [WatsonLemmaRefinementCertificate.size,
    sampleWatsonLemmaRefinementCertificate]

/-- A second-stage Watson-lemma certificate with a named external budget. -/
structure WatsonLemmaBudgetCertificate where
  expansionWindow : ℕ
  laplaceWindow : ℕ
  watsonSlackWindow : ℕ
  watsonBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WatsonLemmaBudgetCertificate.watsonControlled
    (cert : WatsonLemmaBudgetCertificate) : Prop :=
  0 < cert.expansionWindow ∧
    cert.laplaceWindow ≤ cert.expansionWindow + cert.watsonSlackWindow + cert.slack ∧
      cert.watsonBudgetWindow ≤
        cert.expansionWindow + cert.laplaceWindow + cert.watsonSlackWindow + cert.slack

def WatsonLemmaBudgetCertificate.budgetControlled
    (cert : WatsonLemmaBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.expansionWindow + cert.laplaceWindow + cert.watsonSlackWindow +
      cert.watsonBudgetWindow + cert.slack

def watsonLemmaBudgetReady (cert : WatsonLemmaBudgetCertificate) : Prop :=
  cert.watsonControlled ∧ cert.budgetControlled

def WatsonLemmaBudgetCertificate.size
    (cert : WatsonLemmaBudgetCertificate) : ℕ :=
  cert.expansionWindow + cert.laplaceWindow + cert.watsonSlackWindow +
    cert.watsonBudgetWindow + cert.slack

theorem watsonLemma_budgetCertificate_le_size
    (cert : WatsonLemmaBudgetCertificate)
    (h : watsonLemmaBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWatsonLemmaBudgetCertificate :
    WatsonLemmaBudgetCertificate :=
  { expansionWindow := 6, laplaceWindow := 7, watsonSlackWindow := 2,
    watsonBudgetWindow := 16, certificateBudgetWindow := 32, slack := 1 }

example : watsonLemmaBudgetReady sampleWatsonLemmaBudgetCertificate := by
  norm_num [watsonLemmaBudgetReady,
    WatsonLemmaBudgetCertificate.watsonControlled,
    WatsonLemmaBudgetCertificate.budgetControlled,
    sampleWatsonLemmaBudgetCertificate]

example :
    sampleWatsonLemmaBudgetCertificate.certificateBudgetWindow ≤
      sampleWatsonLemmaBudgetCertificate.size := by
  apply watsonLemma_budgetCertificate_le_size
  norm_num [watsonLemmaBudgetReady,
    WatsonLemmaBudgetCertificate.watsonControlled,
    WatsonLemmaBudgetCertificate.budgetControlled,
    sampleWatsonLemmaBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    watsonLemmaBudgetReady sampleWatsonLemmaBudgetCertificate := by
  constructor
  · norm_num [WatsonLemmaBudgetCertificate.watsonControlled,
      sampleWatsonLemmaBudgetCertificate]
  · norm_num [WatsonLemmaBudgetCertificate.budgetControlled,
      sampleWatsonLemmaBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWatsonLemmaBudgetCertificate.certificateBudgetWindow ≤
      sampleWatsonLemmaBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List WatsonLemmaBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleWatsonLemmaBudgetCertificate] =
      true := by
  unfold budgetCertificateListReady sampleWatsonLemmaBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.UniformWatsonLemmaWindows
