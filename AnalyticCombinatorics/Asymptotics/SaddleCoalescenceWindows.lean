import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Saddle coalescence windows.

This module records finite bookkeeping for coalescing saddle windows.
-/

namespace AnalyticCombinatorics.Asymptotics.SaddleCoalescenceWindows

structure SaddleCoalescenceData where
  saddleCount : ℕ
  coalescenceScale : ℕ
  contourSlack : ℕ
deriving DecidableEq, Repr

def hasSaddleCount (d : SaddleCoalescenceData) : Prop :=
  0 < d.saddleCount

def coalescenceScaleControlled (d : SaddleCoalescenceData) : Prop :=
  d.coalescenceScale ≤ d.saddleCount + d.contourSlack

def saddleCoalescenceReady (d : SaddleCoalescenceData) : Prop :=
  hasSaddleCount d ∧ coalescenceScaleControlled d

def saddleCoalescenceBudget (d : SaddleCoalescenceData) : ℕ :=
  d.saddleCount + d.coalescenceScale + d.contourSlack

theorem saddleCoalescenceReady.hasSaddleCount {d : SaddleCoalescenceData}
    (h : saddleCoalescenceReady d) :
    hasSaddleCount d ∧ coalescenceScaleControlled d ∧
      d.coalescenceScale ≤ saddleCoalescenceBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold saddleCoalescenceBudget
  omega

theorem coalescenceScale_le_budget (d : SaddleCoalescenceData) :
    d.coalescenceScale ≤ saddleCoalescenceBudget d := by
  unfold saddleCoalescenceBudget
  omega

def sampleSaddleCoalescenceData : SaddleCoalescenceData :=
  { saddleCount := 6, coalescenceScale := 8, contourSlack := 3 }

example : saddleCoalescenceReady sampleSaddleCoalescenceData := by
  norm_num [saddleCoalescenceReady, hasSaddleCount]
  norm_num [coalescenceScaleControlled, sampleSaddleCoalescenceData]

example : saddleCoalescenceBudget sampleSaddleCoalescenceData = 17 := by
  native_decide

/-- Finite executable readiness audit for saddle coalescence data. -/
def saddleCoalescenceDataListReady
    (data : List SaddleCoalescenceData) : Bool :=
  data.all fun d =>
    0 < d.saddleCount && d.coalescenceScale ≤ d.saddleCount + d.contourSlack

theorem saddleCoalescenceDataList_readyWindow :
    saddleCoalescenceDataListReady
      [{ saddleCount := 4, coalescenceScale := 5, contourSlack := 1 },
       { saddleCount := 6, coalescenceScale := 8, contourSlack := 3 }] = true := by
  unfold saddleCoalescenceDataListReady
  native_decide

structure SaddleCoalescenceCertificateWindow where
  saddleWindow : ℕ
  coalescenceWindow : ℕ
  contourSlack : ℕ
  saddleBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleCoalescenceCertificateWindow.coalescenceControlled
    (w : SaddleCoalescenceCertificateWindow) : Prop :=
  w.coalescenceWindow ≤ w.saddleWindow + w.contourSlack + w.slack

def saddleCoalescenceCertificateReady
    (w : SaddleCoalescenceCertificateWindow) : Prop :=
  0 < w.saddleWindow ∧ w.coalescenceControlled ∧
    w.saddleBudget ≤ w.saddleWindow + w.coalescenceWindow + w.slack

def SaddleCoalescenceCertificateWindow.certificate
    (w : SaddleCoalescenceCertificateWindow) : ℕ :=
  w.saddleWindow + w.coalescenceWindow + w.contourSlack + w.saddleBudget + w.slack

theorem saddleCoalescence_budget_le_certificate
    (w : SaddleCoalescenceCertificateWindow) :
    w.saddleBudget ≤ w.certificate := by
  unfold SaddleCoalescenceCertificateWindow.certificate
  omega

def sampleSaddleCoalescenceCertificateWindow :
    SaddleCoalescenceCertificateWindow :=
  { saddleWindow := 5, coalescenceWindow := 7, contourSlack := 2,
    saddleBudget := 14, slack := 2 }

example : saddleCoalescenceCertificateReady
    sampleSaddleCoalescenceCertificateWindow := by
  norm_num [saddleCoalescenceCertificateReady,
    SaddleCoalescenceCertificateWindow.coalescenceControlled,
    sampleSaddleCoalescenceCertificateWindow]

structure SaddleCoalescenceRefinementCertificate where
  saddleWindow : ℕ
  coalescenceWindow : ℕ
  contourSlackWindow : ℕ
  saddleBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleCoalescenceRefinementCertificate.coalescenceControlled
    (c : SaddleCoalescenceRefinementCertificate) : Prop :=
  c.coalescenceWindow ≤ c.saddleWindow + c.contourSlackWindow + c.slack

def SaddleCoalescenceRefinementCertificate.saddleBudgetControlled
    (c : SaddleCoalescenceRefinementCertificate) : Prop :=
  c.saddleBudgetWindow ≤
    c.saddleWindow + c.coalescenceWindow + c.contourSlackWindow + c.slack

def saddleCoalescenceRefinementReady
    (c : SaddleCoalescenceRefinementCertificate) : Prop :=
  0 < c.saddleWindow ∧
    c.coalescenceControlled ∧
    c.saddleBudgetControlled

def SaddleCoalescenceRefinementCertificate.size
    (c : SaddleCoalescenceRefinementCertificate) : ℕ :=
  c.saddleWindow + c.coalescenceWindow + c.contourSlackWindow + c.slack

theorem saddleCoalescence_saddleBudgetWindow_le_size
    {c : SaddleCoalescenceRefinementCertificate}
    (h : saddleCoalescenceRefinementReady c) :
    c.saddleBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleSaddleCoalescenceRefinementCertificate :
    SaddleCoalescenceRefinementCertificate :=
  { saddleWindow := 5, coalescenceWindow := 7, contourSlackWindow := 2,
    saddleBudgetWindow := 14, slack := 2 }

example : saddleCoalescenceRefinementReady
    sampleSaddleCoalescenceRefinementCertificate := by
  norm_num [saddleCoalescenceRefinementReady,
    SaddleCoalescenceRefinementCertificate.coalescenceControlled,
    SaddleCoalescenceRefinementCertificate.saddleBudgetControlled,
    sampleSaddleCoalescenceRefinementCertificate]

example :
    sampleSaddleCoalescenceRefinementCertificate.saddleBudgetWindow ≤
      sampleSaddleCoalescenceRefinementCertificate.size := by
  norm_num [SaddleCoalescenceRefinementCertificate.size,
    sampleSaddleCoalescenceRefinementCertificate]

/-- A second-stage certificate with the coalescence budget separated from size. -/
structure SaddleCoalescenceBudgetCertificate where
  saddleWindow : ℕ
  coalescenceWindow : ℕ
  contourSlackWindow : ℕ
  saddleBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleCoalescenceBudgetCertificate.coalescenceControlled
    (cert : SaddleCoalescenceBudgetCertificate) : Prop :=
  0 < cert.saddleWindow ∧
    cert.coalescenceWindow ≤ cert.saddleWindow + cert.contourSlackWindow + cert.slack ∧
      cert.saddleBudgetWindow ≤
        cert.saddleWindow + cert.coalescenceWindow + cert.contourSlackWindow + cert.slack

def SaddleCoalescenceBudgetCertificate.budgetControlled
    (cert : SaddleCoalescenceBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.saddleWindow + cert.coalescenceWindow + cert.contourSlackWindow +
      cert.saddleBudgetWindow + cert.slack

def saddleCoalescenceBudgetReady
    (cert : SaddleCoalescenceBudgetCertificate) : Prop :=
  cert.coalescenceControlled ∧ cert.budgetControlled

def SaddleCoalescenceBudgetCertificate.size
    (cert : SaddleCoalescenceBudgetCertificate) : ℕ :=
  cert.saddleWindow + cert.coalescenceWindow + cert.contourSlackWindow +
    cert.saddleBudgetWindow + cert.slack

theorem saddleCoalescence_certificateBudgetWindow_le_size
    (cert : SaddleCoalescenceBudgetCertificate)
    (h : saddleCoalescenceBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSaddleCoalescenceBudgetCertificate :
    SaddleCoalescenceBudgetCertificate :=
  { saddleWindow := 5, coalescenceWindow := 7, contourSlackWindow := 2,
    saddleBudgetWindow := 14, certificateBudgetWindow := 30, slack := 2 }

example :
    saddleCoalescenceBudgetReady sampleSaddleCoalescenceBudgetCertificate := by
  norm_num [saddleCoalescenceBudgetReady,
    SaddleCoalescenceBudgetCertificate.coalescenceControlled,
    SaddleCoalescenceBudgetCertificate.budgetControlled,
    sampleSaddleCoalescenceBudgetCertificate]

example :
    sampleSaddleCoalescenceBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleCoalescenceBudgetCertificate.size := by
  apply saddleCoalescence_certificateBudgetWindow_le_size
  norm_num [saddleCoalescenceBudgetReady,
    SaddleCoalescenceBudgetCertificate.coalescenceControlled,
    SaddleCoalescenceBudgetCertificate.budgetControlled,
    sampleSaddleCoalescenceBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    saddleCoalescenceBudgetReady sampleSaddleCoalescenceBudgetCertificate := by
  constructor
  · norm_num [SaddleCoalescenceBudgetCertificate.coalescenceControlled,
      sampleSaddleCoalescenceBudgetCertificate]
  · norm_num [SaddleCoalescenceBudgetCertificate.budgetControlled,
      sampleSaddleCoalescenceBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddleCoalescenceBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleCoalescenceBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SaddleCoalescenceBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSaddleCoalescenceBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSaddleCoalescenceBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SaddleCoalescenceWindows
