import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix B: Mellin transforms.

Finite fundamental-strip, inversion-line, pole, and residue bookkeeping for
Mellin-transform arguments.
-/

namespace AnalyticCombinatorics.AppB.MellinTransforms

/-- Rational fundamental strip bounds `left < Re(s) < right`. -/
structure FundamentalStrip where
  leftNumerator : ℤ
  leftDenominator : ℕ
  rightNumerator : ℤ
  rightDenominator : ℕ
deriving DecidableEq, Repr

def FundamentalStrip.denominatorsPositive (s : FundamentalStrip) : Prop :=
  0 < s.leftDenominator ∧ 0 < s.rightDenominator

def FundamentalStrip.ordered (s : FundamentalStrip) : Prop :=
  s.leftNumerator * s.rightDenominator <
    s.rightNumerator * s.leftDenominator

def FundamentalStrip.ready (s : FundamentalStrip) : Prop :=
  s.denominatorsPositive ∧ s.ordered

def unitFundamentalStrip : FundamentalStrip :=
  { leftNumerator := 0
    leftDenominator := 1
    rightNumerator := 2
    rightDenominator := 1 }

theorem unitFundamentalStrip_ready :
    unitFundamentalStrip.ready := by
  norm_num [FundamentalStrip.ready, FundamentalStrip.denominatorsPositive,
    FundamentalStrip.ordered, unitFundamentalStrip]

/-- An inversion line inside a finite fundamental strip. -/
structure InversionLineWindow where
  stripLeft : ℤ
  lineAbscissa : ℤ
  stripRight : ℤ
  verticalWindow : ℕ
deriving DecidableEq, Repr

def InversionLineWindow.insideStrip (w : InversionLineWindow) : Prop :=
  w.stripLeft < w.lineAbscissa ∧ w.lineAbscissa < w.stripRight

def InversionLineWindow.ready (w : InversionLineWindow) : Prop :=
  w.insideStrip ∧ 0 < w.verticalWindow

def unitInversionLineWindow : InversionLineWindow :=
  { stripLeft := 0
    lineAbscissa := 1
    stripRight := 2
    verticalWindow := 8 }

theorem unitInversionLineWindow_ready :
    unitInversionLineWindow.ready := by
  norm_num [InversionLineWindow.ready,
    InversionLineWindow.insideStrip, unitInversionLineWindow]

example : unitInversionLineWindow.ready := by
  exact unitInversionLineWindow_ready

/-- Discrete Mellin transform prefix for nonnegative integer samples. -/
def mellinPrefix (a : ℕ → ℕ) (s N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun total n => total + (a n : ℚ) / ((n + 1 : ℚ) ^ s)) 0

theorem mellinPrefix_unit_s2_samples :
    mellinPrefix (fun _ => 1) 2 0 = 1 ∧
      mellinPrefix (fun _ => 1) 2 1 = 5 / 4 ∧
        mellinPrefix (fun _ => 1) 2 2 = 49 / 36 := by
  unfold mellinPrefix
  native_decide

example : mellinPrefix (fun _ => 1) 2 2 = 49 / 36 := by
  unfold mellinPrefix
  native_decide

/-- Finite pole and residue data for Mellin singularity transfer. -/
structure MellinResidueDatum where
  poleNumerator : ℤ
  poleDenominator : ℕ
  poleOrder : ℕ
  residueNumerator : ℤ
  residueDenominator : ℕ
deriving DecidableEq, Repr

def MellinResidueDatum.ready (d : MellinResidueDatum) : Prop :=
  0 < d.poleDenominator ∧ 0 < d.poleOrder ∧ 0 < d.residueDenominator

def unitMellinResidueDatum : MellinResidueDatum :=
  { poleNumerator := 1
    poleDenominator := 1
    poleOrder := 1
    residueNumerator := 1
    residueDenominator := 1 }

theorem unitMellinResidueDatum_ready :
    unitMellinResidueDatum.ready := by
  norm_num [MellinResidueDatum.ready, unitMellinResidueDatum]

/-- Boolean readiness audit for finite Mellin residue data. -/
def mellinResidueListReady
    (data : List MellinResidueDatum) : Bool :=
  data.all fun d =>
    0 < d.poleDenominator && 0 < d.poleOrder && 0 < d.residueDenominator

theorem mellinResidueList_readyWindow :
    mellinResidueListReady
      [unitMellinResidueDatum,
       { poleNumerator := -2, poleDenominator := 1, poleOrder := 2,
         residueNumerator := 3, residueDenominator := 4 }] = true := by
  unfold mellinResidueListReady unitMellinResidueDatum
  native_decide

structure MellinTransformsBudgetCertificate where
  stripWindow : ℕ
  inversionWindow : ℕ
  poleWindow : ℕ
  residueWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinTransformsBudgetCertificate.controlled
    (c : MellinTransformsBudgetCertificate) : Prop :=
  0 < c.stripWindow ∧
    c.inversionWindow ≤ c.stripWindow + c.slack ∧
      c.residueWindow ≤ c.inversionWindow + c.poleWindow + c.slack

def MellinTransformsBudgetCertificate.budgetControlled
    (c : MellinTransformsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.stripWindow + c.inversionWindow + c.poleWindow + c.residueWindow + c.slack

def MellinTransformsBudgetCertificate.Ready
    (c : MellinTransformsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MellinTransformsBudgetCertificate.size
    (c : MellinTransformsBudgetCertificate) : ℕ :=
  c.stripWindow + c.inversionWindow + c.poleWindow + c.residueWindow + c.slack

theorem mellinTransforms_budgetCertificate_le_size
    (c : MellinTransformsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleMellinTransformsBudgetCertificate :
    MellinTransformsBudgetCertificate :=
  { stripWindow := 6
    inversionWindow := 7
    poleWindow := 4
    residueWindow := 12
    certificateBudgetWindow := 30
    slack := 1 }

example : sampleMellinTransformsBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinTransformsBudgetCertificate.controlled,
      sampleMellinTransformsBudgetCertificate]
  · norm_num [MellinTransformsBudgetCertificate.budgetControlled,
      sampleMellinTransformsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMellinTransformsBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinTransformsBudgetCertificate.controlled,
      sampleMellinTransformsBudgetCertificate]
  · norm_num [MellinTransformsBudgetCertificate.budgetControlled,
      sampleMellinTransformsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMellinTransformsBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinTransformsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MellinTransformsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleMellinTransformsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleMellinTransformsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.MellinTransforms
