import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Berry-Esseen windows.

This module records finite bookkeeping for uniform Berry-Esseen error windows.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformBerryEsseenWindows

structure BerryEsseenWindowData where
  momentWindow : ℕ
  varianceWindow : ℕ
  errorWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def varianceWindowPositive (d : BerryEsseenWindowData) : Prop :=
  0 < d.varianceWindow

def berryEsseenErrorControlled (d : BerryEsseenWindowData) : Prop :=
  d.errorWindow ≤ d.momentWindow + d.varianceWindow + d.slack

def berryEsseenWindowReady (d : BerryEsseenWindowData) : Prop :=
  varianceWindowPositive d ∧ berryEsseenErrorControlled d

def berryEsseenWindowBudget (d : BerryEsseenWindowData) : ℕ :=
  d.momentWindow + d.varianceWindow + d.errorWindow + d.slack

theorem berryEsseenWindowReady.error_le_budget
    {d : BerryEsseenWindowData}
    (h : berryEsseenWindowReady d) :
    varianceWindowPositive d ∧ berryEsseenErrorControlled d ∧
      d.errorWindow ≤ berryEsseenWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold berryEsseenWindowBudget
  omega

theorem berryEsseenError_le_budget (d : BerryEsseenWindowData) :
    d.errorWindow ≤ berryEsseenWindowBudget d := by
  unfold berryEsseenWindowBudget
  omega

def sampleBerryEsseenWindowData : BerryEsseenWindowData :=
  { momentWindow := 5, varianceWindow := 4, errorWindow := 8, slack := 1 }

example : berryEsseenWindowReady sampleBerryEsseenWindowData := by
  norm_num [berryEsseenWindowReady, varianceWindowPositive]
  norm_num [berryEsseenErrorControlled, sampleBerryEsseenWindowData]

example : berryEsseenWindowBudget sampleBerryEsseenWindowData = 18 := by
  native_decide

/-- Finite executable readiness audit for Berry-Esseen window data. -/
def berryEsseenDataListReady
    (data : List BerryEsseenWindowData) : Bool :=
  data.all fun d =>
    0 < d.varianceWindow &&
      d.errorWindow ≤ d.momentWindow + d.varianceWindow + d.slack

theorem berryEsseenDataList_readyWindow :
    berryEsseenDataListReady
      [{ momentWindow := 3, varianceWindow := 2, errorWindow := 5, slack := 0 },
       { momentWindow := 5, varianceWindow := 4, errorWindow := 8, slack := 1 }] = true := by
  unfold berryEsseenDataListReady
  native_decide

structure BerryEsseenCertificateWindow where
  momentWindow : ℕ
  varianceWindow : ℕ
  errorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BerryEsseenCertificateWindow.errorControlled
    (w : BerryEsseenCertificateWindow) : Prop :=
  w.errorWindow ≤ w.momentWindow + w.varianceWindow + w.slack

def berryEsseenCertificateReady
    (w : BerryEsseenCertificateWindow) : Prop :=
  0 < w.varianceWindow ∧ w.errorControlled ∧
    w.certificateBudget ≤ w.momentWindow + w.errorWindow + w.slack

def BerryEsseenCertificateWindow.certificate
    (w : BerryEsseenCertificateWindow) : ℕ :=
  w.momentWindow + w.varianceWindow + w.errorWindow +
    w.certificateBudget + w.slack

theorem berryEsseen_certificateBudget_le_certificate
    (w : BerryEsseenCertificateWindow)
    (h : berryEsseenCertificateReady w) :
    w.certificateBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hbudget⟩
  unfold BerryEsseenCertificateWindow.certificate
  omega

def sampleBerryEsseenCertificateWindow :
    BerryEsseenCertificateWindow :=
  { momentWindow := 5, varianceWindow := 4, errorWindow := 8,
    certificateBudget := 14, slack := 1 }

example : berryEsseenCertificateReady sampleBerryEsseenCertificateWindow := by
  norm_num [berryEsseenCertificateReady,
    BerryEsseenCertificateWindow.errorControlled,
    sampleBerryEsseenCertificateWindow]

example :
    sampleBerryEsseenCertificateWindow.certificateBudget ≤
      sampleBerryEsseenCertificateWindow.certificate := by
  apply berryEsseen_certificateBudget_le_certificate
  norm_num [berryEsseenCertificateReady,
    BerryEsseenCertificateWindow.errorControlled,
    sampleBerryEsseenCertificateWindow]

structure BerryEsseenRefinementCertificate where
  momentWindow : ℕ
  varianceWindow : ℕ
  errorWindow : ℕ
  errorBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BerryEsseenRefinementCertificate.errorControlled
    (c : BerryEsseenRefinementCertificate) : Prop :=
  0 < c.varianceWindow ∧
    c.errorWindow ≤ c.momentWindow + c.varianceWindow + c.slack ∧
      c.errorBudgetWindow ≤ c.momentWindow + c.errorWindow + c.slack

def berryEsseenRefinementReady
    (c : BerryEsseenRefinementCertificate) : Prop :=
  c.errorControlled ∧
    c.errorBudgetWindow ≤
      c.momentWindow + c.varianceWindow + c.errorWindow +
        c.errorBudgetWindow + c.slack

def BerryEsseenRefinementCertificate.size
    (c : BerryEsseenRefinementCertificate) : ℕ :=
  c.momentWindow + c.varianceWindow + c.errorWindow + c.slack

theorem berryEsseen_refinementBudget_le_size
    {c : BerryEsseenRefinementCertificate}
    (h : berryEsseenRefinementReady c) :
    c.errorBudgetWindow ≤ c.size := by
  rcases h with ⟨hcontrol, _⟩
  rcases hcontrol with ⟨_, _, hbudget⟩
  unfold BerryEsseenRefinementCertificate.size
  omega

def sampleBerryEsseenRefinementCertificate :
    BerryEsseenRefinementCertificate :=
  { momentWindow := 5, varianceWindow := 4, errorWindow := 8,
    errorBudgetWindow := 14, slack := 1 }

example :
    berryEsseenRefinementReady sampleBerryEsseenRefinementCertificate := by
  norm_num [berryEsseenRefinementReady,
    BerryEsseenRefinementCertificate.errorControlled,
    sampleBerryEsseenRefinementCertificate]

example :
    sampleBerryEsseenRefinementCertificate.errorBudgetWindow ≤
      sampleBerryEsseenRefinementCertificate.size := by
  apply berryEsseen_refinementBudget_le_size
  norm_num [berryEsseenRefinementReady,
    BerryEsseenRefinementCertificate.errorControlled,
    sampleBerryEsseenRefinementCertificate]

/-- A second-stage uniform Berry-Esseen certificate with a named external budget. -/
structure BerryEsseenBudgetCertificate where
  momentWindow : ℕ
  varianceWindow : ℕ
  errorWindow : ℕ
  errorBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BerryEsseenBudgetCertificate.errorControlled
    (cert : BerryEsseenBudgetCertificate) : Prop :=
  0 < cert.varianceWindow ∧
    cert.errorWindow ≤ cert.momentWindow + cert.varianceWindow + cert.slack ∧
      cert.errorBudgetWindow ≤ cert.momentWindow + cert.errorWindow + cert.slack

def BerryEsseenBudgetCertificate.budgetControlled
    (cert : BerryEsseenBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.momentWindow + cert.varianceWindow + cert.errorWindow +
      cert.errorBudgetWindow + cert.slack

def berryEsseenBudgetReady
    (cert : BerryEsseenBudgetCertificate) : Prop :=
  cert.errorControlled ∧ cert.budgetControlled

def BerryEsseenBudgetCertificate.size
    (cert : BerryEsseenBudgetCertificate) : ℕ :=
  cert.momentWindow + cert.varianceWindow + cert.errorWindow +
    cert.errorBudgetWindow + cert.slack

theorem berryEsseen_budgetCertificate_le_size
    (cert : BerryEsseenBudgetCertificate)
    (h : berryEsseenBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  exact h.2

def sampleBerryEsseenBudgetCertificate :
    BerryEsseenBudgetCertificate :=
  { momentWindow := 5, varianceWindow := 4, errorWindow := 8,
    errorBudgetWindow := 14, certificateBudgetWindow := 32, slack := 1 }

example : berryEsseenBudgetReady sampleBerryEsseenBudgetCertificate := by
  norm_num [berryEsseenBudgetReady,
    BerryEsseenBudgetCertificate.errorControlled,
    BerryEsseenBudgetCertificate.budgetControlled,
    sampleBerryEsseenBudgetCertificate]

example :
    sampleBerryEsseenBudgetCertificate.certificateBudgetWindow ≤
      sampleBerryEsseenBudgetCertificate.size := by
  apply berryEsseen_budgetCertificate_le_size
  norm_num [berryEsseenBudgetReady,
    BerryEsseenBudgetCertificate.errorControlled,
    BerryEsseenBudgetCertificate.budgetControlled,
    sampleBerryEsseenBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    berryEsseenBudgetReady sampleBerryEsseenBudgetCertificate := by
  constructor
  · norm_num [BerryEsseenBudgetCertificate.errorControlled,
      sampleBerryEsseenBudgetCertificate]
  · norm_num [BerryEsseenBudgetCertificate.budgetControlled,
      sampleBerryEsseenBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBerryEsseenBudgetCertificate.certificateBudgetWindow ≤
      sampleBerryEsseenBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List BerryEsseenBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBerryEsseenBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleBerryEsseenBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.UniformBerryEsseenWindows
