import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix B: Mellin transform schemas.

Finite strip, pole, and residue-window bookkeeping for Mellin transfers.
-/

namespace AnalyticCombinatorics.AppB.MellinTransformSchemas

/-- Discrete Mellin prefix for finite coefficient samples. -/
def mellinPrefixQ (a : ℕ → ℚ) (s n : ℕ) : ℚ :=
  (List.range (n + 1)).foldl
    (fun total k => total + a k / ((k + 1 : ℚ) ^ s)) 0

/-- Finite pole descriptor for Mellin transfer bookkeeping. -/
structure MellinPole where
  locationNumerator : ℤ
  residueNumerator : ℤ
  order : ℕ
deriving DecidableEq, Repr

def MellinPole.valid (p : MellinPole) : Prop :=
  0 < p.order

/-- Finite check that Mellin prefixes are bounded by a sampled envelope. -/
def mellinPrefixBoundCheck
    (a envelope : ℕ → ℚ) (s N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => mellinPrefixQ a s n ≤ envelope n

theorem unit_mellinPrefixBound :
    mellinPrefixBoundCheck (fun _ => 1) (fun n => n + 1) 2 16 = true := by
  unfold mellinPrefixBoundCheck mellinPrefixQ
  native_decide

theorem simpleMellinPole_valid :
    MellinPole.valid { locationNumerator := 1, residueNumerator := 1, order := 1 } := by
  norm_num [MellinPole.valid]

structure MellinTransformWindow where
  stripWidth : ℕ
  poleCount : ℕ
  residueWindow : ℕ
  verticalSlack : ℕ
deriving DecidableEq, Repr

def mellinTransformWindowReady (w : MellinTransformWindow) : Prop :=
  0 < w.stripWidth ∧
    w.residueWindow ≤ w.stripWidth + w.poleCount + w.verticalSlack

def mellinTransformBudget (w : MellinTransformWindow) : ℕ :=
  w.stripWidth + w.poleCount + w.residueWindow + w.verticalSlack

theorem residueWindow_le_budget (w : MellinTransformWindow) :
    w.residueWindow ≤ mellinTransformBudget w := by
  unfold mellinTransformBudget
  omega

def sampleMellinTransformWindow : MellinTransformWindow :=
  { stripWidth := 4, poleCount := 3, residueWindow := 7, verticalSlack := 1 }

example : mellinTransformWindowReady sampleMellinTransformWindow := by
  norm_num [mellinTransformWindowReady, sampleMellinTransformWindow]

structure MellinTransformSchemasBudgetCertificate where
  stripWindow : ℕ
  poleWindow : ℕ
  residueWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinTransformSchemasBudgetCertificate.controlled
    (c : MellinTransformSchemasBudgetCertificate) : Prop :=
  0 < c.stripWindow ∧
    c.residueWindow ≤ c.stripWindow + c.poleWindow + c.slack

def MellinTransformSchemasBudgetCertificate.budgetControlled
    (c : MellinTransformSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.stripWindow + c.poleWindow + c.residueWindow + c.slack

def MellinTransformSchemasBudgetCertificate.Ready
    (c : MellinTransformSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MellinTransformSchemasBudgetCertificate.size
    (c : MellinTransformSchemasBudgetCertificate) : ℕ :=
  c.stripWindow + c.poleWindow + c.residueWindow + c.slack

theorem mellinTransformSchemas_budgetCertificate_le_size
    (c : MellinTransformSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleMellinTransformSchemasBudgetCertificate :
    MellinTransformSchemasBudgetCertificate :=
  { stripWindow := 4
    poleWindow := 3
    residueWindow := 7
    certificateBudgetWindow := 15
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMellinTransformSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinTransformSchemasBudgetCertificate.controlled,
      sampleMellinTransformSchemasBudgetCertificate]
  · norm_num [MellinTransformSchemasBudgetCertificate.budgetControlled,
      sampleMellinTransformSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMellinTransformSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinTransformSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMellinTransformSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinTransformSchemasBudgetCertificate.controlled,
      sampleMellinTransformSchemasBudgetCertificate]
  · norm_num [MellinTransformSchemasBudgetCertificate.budgetControlled,
      sampleMellinTransformSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MellinTransformSchemasBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleMellinTransformSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleMellinTransformSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.MellinTransformSchemas
