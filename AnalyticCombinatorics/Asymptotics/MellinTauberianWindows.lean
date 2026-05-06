import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Mellin Tauberian windows.

This module records finite bookkeeping for Mellin Tauberian windows.
-/

namespace AnalyticCombinatorics.Asymptotics.MellinTauberianWindows

structure MellinTauberianWindowData where
  mellinStrip : ℕ
  tauberianWindow : ℕ
  residueSlack : ℕ
deriving DecidableEq, Repr

def hasMellinStrip (d : MellinTauberianWindowData) : Prop :=
  0 < d.mellinStrip

def tauberianWindowControlled (d : MellinTauberianWindowData) : Prop :=
  d.tauberianWindow ≤ d.mellinStrip + d.residueSlack

def mellinTauberianReady (d : MellinTauberianWindowData) : Prop :=
  hasMellinStrip d ∧ tauberianWindowControlled d

def mellinTauberianBudget (d : MellinTauberianWindowData) : ℕ :=
  d.mellinStrip + d.tauberianWindow + d.residueSlack

theorem mellinTauberianReady.hasMellinStrip
    {d : MellinTauberianWindowData}
    (h : mellinTauberianReady d) :
    hasMellinStrip d ∧ tauberianWindowControlled d ∧
      d.tauberianWindow ≤ mellinTauberianBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold mellinTauberianBudget
  omega

theorem tauberianWindow_le_budget (d : MellinTauberianWindowData) :
    d.tauberianWindow ≤ mellinTauberianBudget d := by
  unfold mellinTauberianBudget
  omega

def sampleMellinTauberianWindowData : MellinTauberianWindowData :=
  { mellinStrip := 6, tauberianWindow := 8, residueSlack := 3 }

example : mellinTauberianReady sampleMellinTauberianWindowData := by
  norm_num [mellinTauberianReady, hasMellinStrip]
  norm_num [tauberianWindowControlled, sampleMellinTauberianWindowData]

example : mellinTauberianBudget sampleMellinTauberianWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for Mellin-Tauberian window data. -/
def mellinTauberianWindowDataListReady
    (data : List MellinTauberianWindowData) : Bool :=
  data.all fun d => 0 < d.mellinStrip && d.tauberianWindow ≤ d.mellinStrip + d.residueSlack

theorem mellinTauberianWindowDataList_readyWindow :
    mellinTauberianWindowDataListReady
      [{ mellinStrip := 4, tauberianWindow := 5, residueSlack := 1 },
       { mellinStrip := 6, tauberianWindow := 8, residueSlack := 3 }] = true := by
  unfold mellinTauberianWindowDataListReady
  native_decide

/-- A certificate window for Mellin-Tauberian transfer. -/
structure MellinTauberianCertificateWindow where
  stripWindow : ℕ
  tauberianWindow : ℕ
  residueSlack : ℕ
  tauberianBudget : ℕ
  slack : ℕ

/-- The Tauberian window is controlled by the Mellin strip. -/
def mellinTauberianCertificateControlled
    (w : MellinTauberianCertificateWindow) : Prop :=
  w.tauberianWindow ≤ w.stripWindow + w.residueSlack + w.slack

/-- Readiness predicate for a Mellin-Tauberian certificate window. -/
def mellinTauberianCertificateReady
    (w : MellinTauberianCertificateWindow) : Prop :=
  0 < w.stripWindow ∧
    mellinTauberianCertificateControlled w ∧
      w.tauberianBudget ≤ w.stripWindow + w.tauberianWindow + w.slack

/-- Total size of the Mellin-Tauberian certificate. -/
def mellinTauberianCertificate
    (w : MellinTauberianCertificateWindow) : ℕ :=
  w.stripWindow + w.tauberianWindow + w.residueSlack + w.tauberianBudget + w.slack

theorem mellinTauberianCertificate_budget_le_certificate
    (w : MellinTauberianCertificateWindow)
    (h : mellinTauberianCertificateReady w) :
    w.tauberianBudget ≤ mellinTauberianCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold mellinTauberianCertificate
  omega

def sampleMellinTauberianCertificateWindow : MellinTauberianCertificateWindow where
  stripWindow := 6
  tauberianWindow := 7
  residueSlack := 2
  tauberianBudget := 12
  slack := 1

example :
    mellinTauberianCertificateReady sampleMellinTauberianCertificateWindow := by
  norm_num [mellinTauberianCertificateReady,
    mellinTauberianCertificateControlled, sampleMellinTauberianCertificateWindow]

example :
    sampleMellinTauberianCertificateWindow.tauberianBudget ≤
      mellinTauberianCertificate sampleMellinTauberianCertificateWindow := by
  apply mellinTauberianCertificate_budget_le_certificate
  norm_num [mellinTauberianCertificateReady,
    mellinTauberianCertificateControlled, sampleMellinTauberianCertificateWindow]

structure MellinTauberianRefinementCertificate where
  stripWindow : ℕ
  tauberianWindow : ℕ
  residueSlackWindow : ℕ
  tauberianBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinTauberianRefinementCertificate.tauberianControlled
    (c : MellinTauberianRefinementCertificate) : Prop :=
  c.tauberianWindow ≤ c.stripWindow + c.residueSlackWindow + c.slack

def MellinTauberianRefinementCertificate.tauberianBudgetControlled
    (c : MellinTauberianRefinementCertificate) : Prop :=
  c.tauberianBudgetWindow ≤
    c.stripWindow + c.tauberianWindow + c.residueSlackWindow + c.slack

def mellinTauberianRefinementReady
    (c : MellinTauberianRefinementCertificate) : Prop :=
  0 < c.stripWindow ∧ c.tauberianControlled ∧ c.tauberianBudgetControlled

def MellinTauberianRefinementCertificate.size
    (c : MellinTauberianRefinementCertificate) : ℕ :=
  c.stripWindow + c.tauberianWindow + c.residueSlackWindow + c.slack

theorem mellinTauberian_tauberianBudgetWindow_le_size
    {c : MellinTauberianRefinementCertificate}
    (h : mellinTauberianRefinementReady c) :
    c.tauberianBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleMellinTauberianRefinementCertificate :
    MellinTauberianRefinementCertificate :=
  { stripWindow := 6, tauberianWindow := 7, residueSlackWindow := 2,
    tauberianBudgetWindow := 16, slack := 1 }

example : mellinTauberianRefinementReady
    sampleMellinTauberianRefinementCertificate := by
  norm_num [mellinTauberianRefinementReady,
    MellinTauberianRefinementCertificate.tauberianControlled,
    MellinTauberianRefinementCertificate.tauberianBudgetControlled,
    sampleMellinTauberianRefinementCertificate]

example :
    sampleMellinTauberianRefinementCertificate.tauberianBudgetWindow ≤
      sampleMellinTauberianRefinementCertificate.size := by
  norm_num [MellinTauberianRefinementCertificate.size,
    sampleMellinTauberianRefinementCertificate]

/-- A second-stage Mellin-Tauberian certificate with an external budget. -/
structure MellinTauberianBudgetCertificate where
  stripWindow : ℕ
  tauberianWindow : ℕ
  residueSlackWindow : ℕ
  tauberianBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinTauberianBudgetCertificate.tauberianControlled
    (cert : MellinTauberianBudgetCertificate) : Prop :=
  0 < cert.stripWindow ∧
    cert.tauberianWindow ≤ cert.stripWindow + cert.residueSlackWindow + cert.slack ∧
      cert.tauberianBudgetWindow ≤
        cert.stripWindow + cert.tauberianWindow + cert.residueSlackWindow + cert.slack

def MellinTauberianBudgetCertificate.budgetControlled
    (cert : MellinTauberianBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.stripWindow + cert.tauberianWindow + cert.residueSlackWindow +
      cert.tauberianBudgetWindow + cert.slack

def mellinTauberianBudgetReady
    (cert : MellinTauberianBudgetCertificate) : Prop :=
  cert.tauberianControlled ∧ cert.budgetControlled

def MellinTauberianBudgetCertificate.size
    (cert : MellinTauberianBudgetCertificate) : ℕ :=
  cert.stripWindow + cert.tauberianWindow + cert.residueSlackWindow +
    cert.tauberianBudgetWindow + cert.slack

theorem mellinTauberian_certificateBudgetWindow_le_size
    (cert : MellinTauberianBudgetCertificate)
    (h : mellinTauberianBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMellinTauberianBudgetCertificate :
    MellinTauberianBudgetCertificate :=
  { stripWindow := 6, tauberianWindow := 7, residueSlackWindow := 2,
    tauberianBudgetWindow := 16, certificateBudgetWindow := 32, slack := 1 }

example : mellinTauberianBudgetReady sampleMellinTauberianBudgetCertificate := by
  norm_num [mellinTauberianBudgetReady,
    MellinTauberianBudgetCertificate.tauberianControlled,
    MellinTauberianBudgetCertificate.budgetControlled,
    sampleMellinTauberianBudgetCertificate]

example :
    sampleMellinTauberianBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinTauberianBudgetCertificate.size := by
  apply mellinTauberian_certificateBudgetWindow_le_size
  norm_num [mellinTauberianBudgetReady,
    MellinTauberianBudgetCertificate.tauberianControlled,
    MellinTauberianBudgetCertificate.budgetControlled,
    sampleMellinTauberianBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    mellinTauberianBudgetReady sampleMellinTauberianBudgetCertificate := by
  constructor
  · norm_num [MellinTauberianBudgetCertificate.tauberianControlled,
      sampleMellinTauberianBudgetCertificate]
  · norm_num [MellinTauberianBudgetCertificate.budgetControlled,
      sampleMellinTauberianBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMellinTauberianBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinTauberianBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MellinTauberianBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleMellinTauberianBudgetCertificate] =
      true := by
  unfold budgetCertificateListReady sampleMellinTauberianBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.MellinTauberianWindows
