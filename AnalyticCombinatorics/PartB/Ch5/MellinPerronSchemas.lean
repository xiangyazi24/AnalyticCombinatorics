import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Mellin--Perron schemas.

The finite record stores abscissa, vertical cutoff, and residue budget for
Mellin--Perron bookkeeping.
-/

namespace AnalyticCombinatorics.PartB.Ch5.MellinPerronSchemas

structure MellinPerronData where
  abscissa : ℕ
  verticalCutoff : ℕ
  residueBudget : ℕ
deriving DecidableEq, Repr

def abscissaPositive (d : MellinPerronData) : Prop :=
  0 < d.abscissa

def cutoffControlled (d : MellinPerronData) : Prop :=
  d.verticalCutoff ≤ d.abscissa + d.residueBudget

def mellinPerronReady (d : MellinPerronData) : Prop :=
  abscissaPositive d ∧ cutoffControlled d

def mellinPerronBudget (d : MellinPerronData) : ℕ :=
  d.abscissa + d.verticalCutoff + d.residueBudget

theorem mellinPerronReady.abscissa {d : MellinPerronData}
    (h : mellinPerronReady d) :
    abscissaPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem verticalCutoff_le_mellinPerronBudget (d : MellinPerronData) :
    d.verticalCutoff ≤ mellinPerronBudget d := by
  unfold mellinPerronBudget
  omega

def sampleMellinPerronData : MellinPerronData :=
  { abscissa := 5, verticalCutoff := 8, residueBudget := 4 }

example : mellinPerronReady sampleMellinPerronData := by
  norm_num [mellinPerronReady, abscissaPositive]
  norm_num [cutoffControlled, sampleMellinPerronData]

example : mellinPerronBudget sampleMellinPerronData = 17 := by
  native_decide

structure MellinPerronWindow where
  abscissa : ℕ
  verticalCutoff : ℕ
  residueBudget : ℕ
  inversionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinPerronWindow.cutoffControlled (w : MellinPerronWindow) : Prop :=
  w.verticalCutoff ≤ w.abscissa + w.residueBudget + w.slack

def MellinPerronWindow.inversionControlled (w : MellinPerronWindow) : Prop :=
  w.inversionBudget ≤ w.abscissa + w.verticalCutoff + w.residueBudget + w.slack

def mellinPerronWindowReady (w : MellinPerronWindow) : Prop :=
  0 < w.abscissa ∧
    w.cutoffControlled ∧
    w.inversionControlled

def MellinPerronWindow.certificate (w : MellinPerronWindow) : ℕ :=
  w.abscissa + w.verticalCutoff + w.residueBudget + w.slack

theorem mellinPerron_inversionBudget_le_certificate {w : MellinPerronWindow}
    (h : mellinPerronWindowReady w) :
    w.inversionBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hinversion⟩
  exact hinversion

def sampleMellinPerronWindow : MellinPerronWindow :=
  { abscissa := 5, verticalCutoff := 8, residueBudget := 4, inversionBudget := 16, slack := 0 }

example : mellinPerronWindowReady sampleMellinPerronWindow := by
  norm_num [mellinPerronWindowReady, MellinPerronWindow.cutoffControlled,
    MellinPerronWindow.inversionControlled, sampleMellinPerronWindow]

example : sampleMellinPerronWindow.certificate = 17 := by
  native_decide


structure MellinPerronSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinPerronSchemasBudgetCertificate.controlled
    (c : MellinPerronSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MellinPerronSchemasBudgetCertificate.budgetControlled
    (c : MellinPerronSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MellinPerronSchemasBudgetCertificate.Ready
    (c : MellinPerronSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MellinPerronSchemasBudgetCertificate.size
    (c : MellinPerronSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem mellinPerronSchemas_budgetCertificate_le_size
    (c : MellinPerronSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMellinPerronSchemasBudgetCertificate :
    MellinPerronSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMellinPerronSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinPerronSchemasBudgetCertificate.controlled,
      sampleMellinPerronSchemasBudgetCertificate]
  · norm_num [MellinPerronSchemasBudgetCertificate.budgetControlled,
      sampleMellinPerronSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMellinPerronSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinPerronSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMellinPerronSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinPerronSchemasBudgetCertificate.controlled,
      sampleMellinPerronSchemasBudgetCertificate]
  · norm_num [MellinPerronSchemasBudgetCertificate.budgetControlled,
      sampleMellinPerronSchemasBudgetCertificate]

example :
    sampleMellinPerronSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinPerronSchemasBudgetCertificate.size := by
  apply mellinPerronSchemas_budgetCertificate_le_size
  constructor
  · norm_num [MellinPerronSchemasBudgetCertificate.controlled,
      sampleMellinPerronSchemasBudgetCertificate]
  · norm_num [MellinPerronSchemasBudgetCertificate.budgetControlled,
      sampleMellinPerronSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MellinPerronSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMellinPerronSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMellinPerronSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.MellinPerronSchemas
