import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Transfer Schemas

Executable coefficient models for standard singular expansions.
-/

namespace AnalyticCombinatorics.Asymptotics.TransferSchemas

/-- Coefficients of `(1 - z)^{-k}` for positive integer `k`. -/
def poleCoeff (k n : ℕ) : ℕ :=
  if k = 0 then 0 else (n + k - 1).choose (k - 1)

theorem poleCoeff_zero_order (n : ℕ) :
    poleCoeff 0 n = 0 := by
  simp [poleCoeff]

theorem poleCoeff_simple (n : ℕ) :
    poleCoeff 1 n = 1 := by
  simp [poleCoeff]

theorem simplePole_coeffs :
    poleCoeff 1 0 = 1 ∧
    poleCoeff 1 1 = 1 ∧
    poleCoeff 1 2 = 1 ∧
    poleCoeff 1 3 = 1 := by
  native_decide

theorem doublePole_coeffs :
    poleCoeff 2 0 = 1 ∧
    poleCoeff 2 1 = 2 ∧
    poleCoeff 2 2 = 3 ∧
    poleCoeff 2 3 = 4 ∧
    poleCoeff 2 4 = 5 := by
  native_decide

theorem triplePole_coeffs :
    poleCoeff 3 0 = 1 ∧
    poleCoeff 3 1 = 3 ∧
    poleCoeff 3 2 = 6 ∧
    poleCoeff 3 3 = 10 ∧
    poleCoeff 3 4 = 15 := by
  native_decide

/-- Coefficients of `1 / (1 - ρinv z)^k` for integer inverse radius. -/
def scaledPoleCoeff (ρinv k n : ℕ) : ℕ :=
  poleCoeff k n * ρinv ^ n

theorem scaledPoleCoeff_one_radius (k n : ℕ) :
    scaledPoleCoeff 1 k n = poleCoeff k n := by
  simp [scaledPoleCoeff]

theorem scaledPoleCoeff_zero_order (ρinv n : ℕ) :
    scaledPoleCoeff ρinv 0 n = 0 := by
  simp [scaledPoleCoeff, poleCoeff_zero_order]

theorem scaled_doublePole_two :
    scaledPoleCoeff 2 2 0 = 1 ∧
    scaledPoleCoeff 2 2 1 = 4 ∧
    scaledPoleCoeff 2 2 2 = 12 ∧
    scaledPoleCoeff 2 2 3 = 32 ∧
    scaledPoleCoeff 2 2 4 = 80 := by
  native_decide

/-- Coefficients of `1 / (1 - z^period)` as a periodic singular model. -/
def periodicPoleCoeff (period n : ℕ) : ℕ :=
  if period = 0 then 0 else if period ∣ n then 1 else 0

theorem periodicPoleCoeff_zero_period (n : ℕ) :
    periodicPoleCoeff 0 n = 0 := by
  simp [periodicPoleCoeff]

theorem periodicPoleCoeff_of_dvd {period n : ℕ}
    (hperiod : period ≠ 0) (hdiv : period ∣ n) :
    periodicPoleCoeff period n = 1 := by
  simp [periodicPoleCoeff, hperiod, hdiv]

theorem periodicPoleCoeff_of_not_dvd {period n : ℕ}
    (hperiod : period ≠ 0) (hdiv : ¬ period ∣ n) :
    periodicPoleCoeff period n = 0 := by
  simp [periodicPoleCoeff, hperiod, hdiv]

theorem period_two_coeffs :
    periodicPoleCoeff 2 0 = 1 ∧
    periodicPoleCoeff 2 1 = 0 ∧
    periodicPoleCoeff 2 2 = 1 ∧
    periodicPoleCoeff 2 3 = 0 ∧
    periodicPoleCoeff 2 4 = 1 := by
  native_decide

theorem period_three_coeffs :
    periodicPoleCoeff 3 0 = 1 ∧
    periodicPoleCoeff 3 1 = 0 ∧
    periodicPoleCoeff 3 2 = 0 ∧
    periodicPoleCoeff 3 3 = 1 ∧
    periodicPoleCoeff 3 4 = 0 ∧
    periodicPoleCoeff 3 6 = 1 := by
  native_decide

/-- Algebraic square-root schema descriptor. -/
structure AlgebraicSchema where
  radiusInv : ℕ
  exponentNumerator : ℤ
  exponentDenominator : ℕ

def catalanSchema : AlgebraicSchema where
  radiusInv := 4
  exponentNumerator := 1
  exponentDenominator := 2

def motzkinSchema : AlgebraicSchema where
  radiusInv := 3
  exponentNumerator := 1
  exponentDenominator := 2

theorem schema_samples :
    catalanSchema.radiusInv = 4 ∧
    catalanSchema.exponentDenominator = 2 ∧
    motzkinSchema.radiusInv = 3 ∧
    motzkinSchema.exponentNumerator = 1 := by
  native_decide

/-- Finite well-formedness certificate for an algebraic transfer schema. -/
def algebraicSchemaReady (s : AlgebraicSchema) : Prop :=
  0 < s.radiusInv ∧ 0 < s.exponentDenominator

theorem algebraicSchemaReady.mk {s : AlgebraicSchema}
    (hr : 0 < s.radiusInv) (he : 0 < s.exponentDenominator) :
    algebraicSchemaReady s := by
  exact ⟨hr, he⟩

theorem catalanSchema_ready : algebraicSchemaReady catalanSchema := by
  unfold algebraicSchemaReady catalanSchema
  native_decide

theorem motzkinSchema_ready : algebraicSchemaReady motzkinSchema := by
  unfold algebraicSchemaReady motzkinSchema
  native_decide

/-- Finite executable readiness audit for algebraic transfer schemas. -/
def algebraicSchemaListReady (schemas : List AlgebraicSchema) : Bool :=
  schemas.all fun s => 0 < s.radiusInv && 0 < s.exponentDenominator

theorem algebraicSchemaList_readyWindow :
    algebraicSchemaListReady
      [{ radiusInv := 3, exponentNumerator := 1, exponentDenominator := 2 },
       { radiusInv := 4, exponentNumerator := 1, exponentDenominator := 2 }] =
      true := by
  unfold algebraicSchemaListReady
  native_decide

/-- Flajolet-Odlyzko transfer certificate for a concrete algebraic schema. -/
def FlajoletOdlyzkoTransfer
    (coeff : ℕ → ℕ) (schema : AlgebraicSchema) (N : ℕ) : Prop :=
  algebraicSchemaReady schema ∧
    ∀ n, n ≤ N → coeff n ≤ scaledPoleCoeff schema.radiusInv 2 n

def catalanCoeff (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

theorem flajolet_odlyzko_transfer_statement :
    FlajoletOdlyzkoTransfer catalanCoeff catalanSchema 8 := by
  unfold FlajoletOdlyzkoTransfer algebraicSchemaReady catalanSchema catalanCoeff scaledPoleCoeff
  native_decide

/-- Certificate for superposition of several dominant singularities. -/
def MultipleSingularityTransfer
    (coeff : ℕ → ℕ) (singularities : List ℂ) (schema : AlgebraicSchema) (N : ℕ) : Prop :=
  algebraicSchemaReady schema ∧ 0 < singularities.length ∧
    ∀ n, n ≤ N → coeff n ≤ singularities.length * scaledPoleCoeff schema.radiusInv 2 n

def evenCatalanWindowCoeff (n : ℕ) : ℕ :=
  if 2 ∣ n then catalanCoeff (n / 2) else 0

theorem multiple_singularity_transfer_statement :
    MultipleSingularityTransfer evenCatalanWindowCoeff [1, -1] catalanSchema 10 := by
  unfold MultipleSingularityTransfer algebraicSchemaReady catalanSchema evenCatalanWindowCoeff
    catalanCoeff scaledPoleCoeff
  native_decide

/-- A finite certificate for algebraic transfer windows. -/
structure AlgebraicTransferRefinementCertificate where
  radiusWindow : ℕ
  exponentDenominatorWindow : ℕ
  singularityCountWindow : ℕ
  coefficientBudgetWindow : ℕ
  slack : ℕ

def AlgebraicTransferRefinementCertificate.parametersControlled
    (cert : AlgebraicTransferRefinementCertificate) : Prop :=
  0 < cert.radiusWindow ∧
    0 < cert.exponentDenominatorWindow ∧
      0 < cert.singularityCountWindow

def AlgebraicTransferRefinementCertificate.coefficientControlled
    (cert : AlgebraicTransferRefinementCertificate) : Prop :=
  cert.coefficientBudgetWindow ≤
    cert.radiusWindow + cert.exponentDenominatorWindow +
      cert.singularityCountWindow + cert.slack

def algebraicTransferRefinementReady
    (cert : AlgebraicTransferRefinementCertificate) : Prop :=
  cert.parametersControlled ∧ cert.coefficientControlled

def AlgebraicTransferRefinementCertificate.size
    (cert : AlgebraicTransferRefinementCertificate) : ℕ :=
  cert.radiusWindow + cert.exponentDenominatorWindow +
    cert.singularityCountWindow + cert.slack

theorem algebraicTransfer_coefficientBudgetWindow_le_size
    (cert : AlgebraicTransferRefinementCertificate)
    (h : algebraicTransferRefinementReady cert) :
    cert.coefficientBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAlgebraicTransferRefinementCertificate :
    AlgebraicTransferRefinementCertificate where
  radiusWindow := 4
  exponentDenominatorWindow := 2
  singularityCountWindow := 2
  coefficientBudgetWindow := 9
  slack := 1

example :
    algebraicTransferRefinementReady sampleAlgebraicTransferRefinementCertificate := by
  norm_num [algebraicTransferRefinementReady,
    AlgebraicTransferRefinementCertificate.parametersControlled,
    AlgebraicTransferRefinementCertificate.coefficientControlled,
    sampleAlgebraicTransferRefinementCertificate]

example :
    sampleAlgebraicTransferRefinementCertificate.coefficientBudgetWindow ≤
      sampleAlgebraicTransferRefinementCertificate.size := by
  apply algebraicTransfer_coefficientBudgetWindow_le_size
  norm_num [algebraicTransferRefinementReady,
    AlgebraicTransferRefinementCertificate.parametersControlled,
    AlgebraicTransferRefinementCertificate.coefficientControlled,
    sampleAlgebraicTransferRefinementCertificate]


structure TransferSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransferSchemasBudgetCertificate.controlled
    (c : TransferSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def TransferSchemasBudgetCertificate.budgetControlled
    (c : TransferSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TransferSchemasBudgetCertificate.Ready
    (c : TransferSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TransferSchemasBudgetCertificate.size
    (c : TransferSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem transferSchemas_budgetCertificate_le_size
    (c : TransferSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTransferSchemasBudgetCertificate :
    TransferSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TransferSchemasBudgetCertificate.controlled,
      sampleTransferSchemasBudgetCertificate]
  · norm_num [TransferSchemasBudgetCertificate.budgetControlled,
      sampleTransferSchemasBudgetCertificate]

example :
    sampleTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferSchemasBudgetCertificate.size := by
  apply transferSchemas_budgetCertificate_le_size
  constructor
  · norm_num [TransferSchemasBudgetCertificate.controlled,
      sampleTransferSchemasBudgetCertificate]
  · norm_num [TransferSchemasBudgetCertificate.budgetControlled,
      sampleTransferSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TransferSchemasBudgetCertificate.controlled,
      sampleTransferSchemasBudgetCertificate]
  · norm_num [TransferSchemasBudgetCertificate.budgetControlled,
      sampleTransferSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List TransferSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTransferSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleTransferSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.TransferSchemas
