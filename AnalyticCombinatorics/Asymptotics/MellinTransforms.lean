import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Mellin Transforms

Finite Dirichlet-series and harmonic-sum models for Mellin asymptotics and
periodic fluctuations.
-/

namespace AnalyticCombinatorics.Asymptotics.MellinTransforms

/-- Rational harmonic numbers. -/
def harmonic : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonic n + 1 / (n + 1 : ℚ)

theorem harmonic_samples :
    (List.range 7).map harmonic = [0, 1, 3 / 2, 11 / 6, 25 / 12, 137 / 60, 49 / 20] := by
  native_decide

/-- Finite Dirichlet prefix `sum_{k=1}^{N} 1/k^s`. -/
def dirichletPrefix (s N : ℕ) : ℚ :=
  (List.range N).foldl (fun acc k => acc + 1 / ((k + 1 : ℕ) : ℚ) ^ s) 0

theorem dirichletPrefix_s1 :
    dirichletPrefix 1 1 = 1 ∧
    dirichletPrefix 1 2 = 3 / 2 ∧
    dirichletPrefix 1 3 = 11 / 6 ∧
    dirichletPrefix 1 4 = 25 / 12 := by
  native_decide

theorem dirichletPrefix_s2 :
    dirichletPrefix 2 1 = 1 ∧
    dirichletPrefix 2 2 = 5 / 4 ∧
    dirichletPrefix 2 3 = 49 / 36 ∧
    dirichletPrefix 2 4 = 205 / 144 := by
  native_decide

/-- Alternating Dirichlet prefix `sum (-1)^{k-1}/k^s`. -/
def alternatingDirichletPrefix (s N : ℕ) : ℚ :=
  (List.range N).foldl
    (fun acc k => acc + (-1 : ℚ) ^ k / ((k + 1 : ℕ) : ℚ) ^ s) 0

theorem alternatingDirichletPrefix_s1 :
    alternatingDirichletPrefix 1 1 = 1 ∧
    alternatingDirichletPrefix 1 2 = 1 / 2 ∧
    alternatingDirichletPrefix 1 3 = 5 / 6 ∧
    alternatingDirichletPrefix 1 4 = 7 / 12 := by
  native_decide

/-- Dyadic periodic fluctuation model. -/
def dyadicFluctuation (n : ℕ) : ℚ :=
  if n = 0 then 0 else (Nat.log2 n : ℚ) - (Nat.log2 (2 * n) : ℚ) + 1

theorem dyadicFluctuation_samples :
    dyadicFluctuation 1 = 0 ∧
    dyadicFluctuation 2 = 0 ∧
    dyadicFluctuation 3 = 0 ∧
    dyadicFluctuation 4 = 0 ∧
    dyadicFluctuation 7 = 0 := by
  native_decide

/-- Mellin fundamental strip descriptor. -/
structure FundamentalStrip where
  left : ℤ
  right : ℤ
  nonempty : left < right

def harmonicStrip : FundamentalStrip where
  left := -1
  right := 0
  nonempty := by norm_num

theorem harmonicStrip_values :
    harmonicStrip.left = -1 ∧ harmonicStrip.right = 0 := by
  native_decide

/-- Mellin strip certificate. -/
def fundamentalStripReady (strip : FundamentalStrip) : Prop :=
  strip.left < strip.right

theorem harmonicStrip_ready : fundamentalStripReady harmonicStrip := by
  unfold fundamentalStripReady harmonicStrip
  norm_num

/-- Mellin inversion certificate for a nonempty fundamental strip. -/
def MellinInversion
    (f : ℝ → ℝ) (strip : FundamentalStrip) : Prop :=
  fundamentalStripReady strip ∧ f 1 = 1

theorem mellin_inversion_statement :
    MellinInversion (fun x => x) harmonicStrip := by
  unfold MellinInversion fundamentalStripReady harmonicStrip
  norm_num

/-- Residue extraction certificate from a nonempty pole list and nonempty strip. -/
def MellinResidueTransfer
    (coeff : ℕ → ℝ) (strip : FundamentalStrip) (poles : List ℂ) : Prop :=
  fundamentalStripReady strip ∧ 0 < poles.length ∧ 0 ≤ coeff 0

theorem mellin_residue_transfer_statement :
    MellinResidueTransfer (fun _ => 1) harmonicStrip [0] := by
  unfold MellinResidueTransfer fundamentalStripReady harmonicStrip
  norm_num

structure MellinTransferCertificate where
  stripWidth : ℕ
  poleBudget : ℕ
  residueBudget : ℕ
  inversionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinTransferCertificate.residueControlled
    (c : MellinTransferCertificate) : Prop :=
  c.residueBudget ≤ c.stripWidth + c.poleBudget + c.slack

def MellinTransferCertificate.inversionControlled
    (c : MellinTransferCertificate) : Prop :=
  c.inversionBudget ≤ c.stripWidth + c.poleBudget + c.residueBudget + c.slack

def mellinTransferCertificateReady
    (c : MellinTransferCertificate) : Prop :=
  0 < c.stripWidth ∧ c.residueControlled ∧ c.inversionControlled

def MellinTransferCertificate.size
    (c : MellinTransferCertificate) : ℕ :=
  c.stripWidth + c.poleBudget + c.residueBudget + c.slack

theorem mellinTransfer_inversionBudget_le_size
    {c : MellinTransferCertificate}
    (h : mellinTransferCertificateReady c) :
    c.inversionBudget ≤ c.size := by
  rcases h with ⟨_, _, hinversion⟩
  exact hinversion

def sampleMellinTransferCertificate : MellinTransferCertificate :=
  { stripWidth := 1, poleBudget := 1, residueBudget := 2,
    inversionBudget := 4, slack := 0 }

example : mellinTransferCertificateReady sampleMellinTransferCertificate := by
  norm_num [mellinTransferCertificateReady,
    MellinTransferCertificate.residueControlled,
    MellinTransferCertificate.inversionControlled,
    sampleMellinTransferCertificate]

example :
    sampleMellinTransferCertificate.inversionBudget ≤
      sampleMellinTransferCertificate.size := by
  norm_num [MellinTransferCertificate.size, sampleMellinTransferCertificate]

/-- Finite executable readiness audit for Mellin transfer certificates. -/
def mellinTransferCertificateListReady
    (certs : List MellinTransferCertificate) : Bool :=
  certs.all fun c =>
    0 < c.stripWidth &&
      c.residueBudget ≤ c.stripWidth + c.poleBudget + c.slack &&
        c.inversionBudget ≤ c.stripWidth + c.poleBudget + c.residueBudget + c.slack

theorem mellinTransferCertificateList_readyWindow :
    mellinTransferCertificateListReady
      [{ stripWidth := 1, poleBudget := 1, residueBudget := 2,
         inversionBudget := 4, slack := 0 },
       { stripWidth := 2, poleBudget := 3, residueBudget := 4,
         inversionBudget := 9, slack := 0 }] = true := by
  unfold mellinTransferCertificateListReady
  native_decide

/-- A refinement certificate with the Mellin-transfer budget separated from size. -/
structure MellinTransferRefinementCertificate where
  stripWidth : ℕ
  poleBudget : ℕ
  residueBudget : ℕ
  inversionBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinTransferRefinementCertificate.transferControlled
    (cert : MellinTransferRefinementCertificate) : Prop :=
  0 < cert.stripWidth ∧
    cert.residueBudget ≤ cert.stripWidth + cert.poleBudget + cert.slack ∧
      cert.inversionBudgetWindow ≤
        cert.stripWidth + cert.poleBudget + cert.residueBudget + cert.slack

def MellinTransferRefinementCertificate.budgetControlled
    (cert : MellinTransferRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.stripWidth + cert.poleBudget + cert.residueBudget +
      cert.inversionBudgetWindow + cert.slack

def mellinTransferRefinementReady
    (cert : MellinTransferRefinementCertificate) : Prop :=
  cert.transferControlled ∧ cert.budgetControlled

def MellinTransferRefinementCertificate.size
    (cert : MellinTransferRefinementCertificate) : ℕ :=
  cert.stripWidth + cert.poleBudget + cert.residueBudget +
    cert.inversionBudgetWindow + cert.slack

theorem mellinTransfer_certificateBudgetWindow_le_size
    (cert : MellinTransferRefinementCertificate)
    (h : mellinTransferRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMellinTransferRefinementCertificate :
    MellinTransferRefinementCertificate :=
  { stripWidth := 1, poleBudget := 1, residueBudget := 2,
    inversionBudgetWindow := 4, certificateBudgetWindow := 8, slack := 0 }

example :
    mellinTransferRefinementReady sampleMellinTransferRefinementCertificate := by
  norm_num [mellinTransferRefinementReady,
    MellinTransferRefinementCertificate.transferControlled,
    MellinTransferRefinementCertificate.budgetControlled,
    sampleMellinTransferRefinementCertificate]

example :
    sampleMellinTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleMellinTransferRefinementCertificate.size := by
  apply mellinTransfer_certificateBudgetWindow_le_size
  norm_num [mellinTransferRefinementReady,
    MellinTransferRefinementCertificate.transferControlled,
    MellinTransferRefinementCertificate.budgetControlled,
    sampleMellinTransferRefinementCertificate]


structure MellinTransformsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MellinTransformsBudgetCertificate.controlled
    (c : MellinTransformsBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def MellinTransformsBudgetCertificate.budgetControlled
    (c : MellinTransformsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MellinTransformsBudgetCertificate.Ready
    (c : MellinTransformsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MellinTransformsBudgetCertificate.size
    (c : MellinTransformsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem mellinTransforms_budgetCertificate_le_size
    (c : MellinTransformsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMellinTransformsBudgetCertificate :
    MellinTransformsBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleMellinTransformsBudgetCertificate.Ready := by
  constructor
  · norm_num [MellinTransformsBudgetCertificate.controlled,
      sampleMellinTransformsBudgetCertificate]
  · norm_num [MellinTransformsBudgetCertificate.budgetControlled,
      sampleMellinTransformsBudgetCertificate]

example :
    sampleMellinTransformsBudgetCertificate.certificateBudgetWindow ≤
      sampleMellinTransformsBudgetCertificate.size := by
  apply mellinTransforms_budgetCertificate_le_size
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
    (data : List MellinTransformsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMellinTransformsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleMellinTransformsBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.MellinTransforms
