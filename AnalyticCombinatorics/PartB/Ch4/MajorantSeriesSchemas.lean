import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Majorant-series schemas for coefficient bounds.

The file records elementary pointwise domination and finite prefix estimates
used by analytic coefficient majorants.
-/

namespace AnalyticCombinatorics.PartB.Ch4.MajorantSeriesSchemas

def pointwiseLe (a b : ℕ → ℕ) : Prop :=
  ∀ n, a n ≤ b n

def prefixMass (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).map a |>.sum

def constantSeries (c : ℕ) (n : ℕ) : ℕ := c + (n - n)

theorem pointwiseLe_refl (a : ℕ → ℕ) :
    pointwiseLe a a := by
  intro n
  rfl

theorem pointwiseLe_trans {a b c : ℕ → ℕ}
    (hab : pointwiseLe a b) (hbc : pointwiseLe b c) :
    pointwiseLe a c := by
  intro n
  exact le_trans (hab n) (hbc n)

theorem prefixMass_zero (a : ℕ → ℕ) :
    prefixMass a 0 = a 0 := by
  simp [prefixMass]

example : prefixMass (constantSeries 3) 4 = 15 := by
  native_decide

example : pointwiseLe (constantSeries 2) (constantSeries 5) := by
  intro n
  norm_num [constantSeries]

structure MajorantWindow where
  cutoff : ℕ
  coefficientMass : ℕ
  majorantMass : ℕ
  tailSlack : ℕ
deriving DecidableEq, Repr

def MajorantWindow.ready (w : MajorantWindow) : Prop :=
  w.coefficientMass ≤ w.majorantMass + w.tailSlack

def MajorantWindow.prefixBudget (w : MajorantWindow) : ℕ :=
  w.majorantMass + w.tailSlack

def MajorantWindow.certificate (w : MajorantWindow) : ℕ :=
  w.cutoff + w.coefficientMass + w.majorantMass + w.tailSlack

theorem coefficientMass_le_certificate (w : MajorantWindow) :
    w.coefficientMass ≤ w.certificate := by
  unfold MajorantWindow.certificate
  omega

def sampleMajorantWindow : MajorantWindow :=
  { cutoff := 4, coefficientMass := 10, majorantMass := 15, tailSlack := 0 }

example : sampleMajorantWindow.ready := by
  norm_num [sampleMajorantWindow, MajorantWindow.ready]

example : sampleMajorantWindow.prefixBudget = 15 := by
  native_decide


structure MajorantSeriesSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MajorantSeriesSchemasBudgetCertificate.controlled
    (c : MajorantSeriesSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MajorantSeriesSchemasBudgetCertificate.budgetControlled
    (c : MajorantSeriesSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MajorantSeriesSchemasBudgetCertificate.Ready
    (c : MajorantSeriesSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MajorantSeriesSchemasBudgetCertificate.size
    (c : MajorantSeriesSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem majorantSeriesSchemas_budgetCertificate_le_size
    (c : MajorantSeriesSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMajorantSeriesSchemasBudgetCertificate :
    MajorantSeriesSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleMajorantSeriesSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MajorantSeriesSchemasBudgetCertificate.controlled,
      sampleMajorantSeriesSchemasBudgetCertificate]
  · norm_num [MajorantSeriesSchemasBudgetCertificate.budgetControlled,
      sampleMajorantSeriesSchemasBudgetCertificate]

example :
    sampleMajorantSeriesSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMajorantSeriesSchemasBudgetCertificate.size := by
  apply majorantSeriesSchemas_budgetCertificate_le_size
  constructor
  · norm_num [MajorantSeriesSchemasBudgetCertificate.controlled,
      sampleMajorantSeriesSchemasBudgetCertificate]
  · norm_num [MajorantSeriesSchemasBudgetCertificate.budgetControlled,
      sampleMajorantSeriesSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMajorantSeriesSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MajorantSeriesSchemasBudgetCertificate.controlled,
      sampleMajorantSeriesSchemasBudgetCertificate]
  · norm_num [MajorantSeriesSchemasBudgetCertificate.budgetControlled,
      sampleMajorantSeriesSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMajorantSeriesSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMajorantSeriesSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MajorantSeriesSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMajorantSeriesSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMajorantSeriesSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.MajorantSeriesSchemas
