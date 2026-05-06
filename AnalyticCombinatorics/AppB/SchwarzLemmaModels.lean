import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Schwarz-lemma-style finite norm models.

Analytic norm inequalities are represented by natural-number budgets, which
are enough for later coefficient-bound bookkeeping.
-/

namespace AnalyticCombinatorics.AppB.SchwarzLemmaModels

structure DiskMapBound where
  valueAtZero : ℕ
  derivativeNorm : ℕ
  radiusBound : ℕ
deriving DecidableEq, Repr

def normalizedAtZero (b : DiskMapBound) : Prop :=
  b.valueAtZero = 0

def schwarzBounded (b : DiskMapBound) : Prop :=
  normalizedAtZero b ∧ b.derivativeNorm ≤ b.radiusBound

def derivativeSlack (b : DiskMapBound) : ℕ :=
  b.radiusBound - b.derivativeNorm

theorem schwarzBounded.normalized {b : DiskMapBound}
    (h : schwarzBounded b) :
    normalizedAtZero b ∧ b.derivativeNorm ≤ b.radiusBound := by
  refine ⟨h.1, h.2⟩

theorem derivativeSlack_add {b : DiskMapBound}
    (h : b.derivativeNorm ≤ b.radiusBound) :
    derivativeSlack b + b.derivativeNorm = b.radiusBound := by
  unfold derivativeSlack
  omega

def sampleDiskMap : DiskMapBound :=
  { valueAtZero := 0, derivativeNorm := 3, radiusBound := 5 }

example : schwarzBounded sampleDiskMap := by
  norm_num [schwarzBounded, normalizedAtZero, sampleDiskMap]

example : derivativeSlack sampleDiskMap = 2 := by
  native_decide

structure SchwarzWindow where
  valueAtZero : ℕ
  derivativeNorm : ℕ
  radiusBound : ℕ
  coefficientBound : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SchwarzWindow.normalized (w : SchwarzWindow) : Prop :=
  w.valueAtZero = 0

def SchwarzWindow.derivativeControlled (w : SchwarzWindow) : Prop :=
  w.derivativeNorm ≤ w.radiusBound + w.slack

def SchwarzWindow.coefficientControlled (w : SchwarzWindow) : Prop :=
  w.coefficientBound ≤ w.radiusBound + w.derivativeNorm + w.slack

def SchwarzWindow.ready (w : SchwarzWindow) : Prop :=
  w.normalized ∧ w.derivativeControlled ∧ w.coefficientControlled

def SchwarzWindow.certificate (w : SchwarzWindow) : ℕ :=
  w.valueAtZero + w.derivativeNorm + w.radiusBound + w.coefficientBound + w.slack

theorem coefficientBound_le_certificate (w : SchwarzWindow) :
    w.coefficientBound ≤ w.certificate := by
  unfold SchwarzWindow.certificate
  omega

def sampleSchwarzWindow : SchwarzWindow :=
  { valueAtZero := 0, derivativeNorm := 3, radiusBound := 5, coefficientBound := 7, slack := 0 }

example : sampleSchwarzWindow.ready := by
  norm_num [sampleSchwarzWindow, SchwarzWindow.ready, SchwarzWindow.normalized,
    SchwarzWindow.derivativeControlled, SchwarzWindow.coefficientControlled]


structure SchwarzLemmaModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SchwarzLemmaModelsBudgetCertificate.controlled
    (c : SchwarzLemmaModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SchwarzLemmaModelsBudgetCertificate.budgetControlled
    (c : SchwarzLemmaModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SchwarzLemmaModelsBudgetCertificate.Ready
    (c : SchwarzLemmaModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SchwarzLemmaModelsBudgetCertificate.size
    (c : SchwarzLemmaModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem schwarzLemmaModels_budgetCertificate_le_size
    (c : SchwarzLemmaModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSchwarzLemmaModelsBudgetCertificate :
    SchwarzLemmaModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSchwarzLemmaModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [SchwarzLemmaModelsBudgetCertificate.controlled,
      sampleSchwarzLemmaModelsBudgetCertificate]
  · norm_num [SchwarzLemmaModelsBudgetCertificate.budgetControlled,
      sampleSchwarzLemmaModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSchwarzLemmaModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleSchwarzLemmaModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSchwarzLemmaModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [SchwarzLemmaModelsBudgetCertificate.controlled,
      sampleSchwarzLemmaModelsBudgetCertificate]
  · norm_num [SchwarzLemmaModelsBudgetCertificate.budgetControlled,
      sampleSchwarzLemmaModelsBudgetCertificate]

example :
    sampleSchwarzLemmaModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleSchwarzLemmaModelsBudgetCertificate.size := by
  apply schwarzLemmaModels_budgetCertificate_le_size
  constructor
  · norm_num [SchwarzLemmaModelsBudgetCertificate.controlled,
      sampleSchwarzLemmaModelsBudgetCertificate]
  · norm_num [SchwarzLemmaModelsBudgetCertificate.budgetControlled,
      sampleSchwarzLemmaModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SchwarzLemmaModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSchwarzLemmaModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSchwarzLemmaModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.SchwarzLemmaModels
