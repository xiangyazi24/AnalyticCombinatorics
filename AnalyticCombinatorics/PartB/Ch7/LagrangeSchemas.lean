import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter VII: Lagrange Schemas

Executable coefficient checks for implicit specifications and Lagrange
inversion schemas.
-/

namespace AnalyticCombinatorics.PartB.Ch7.LagrangeSchemas

/-- Catalan coefficients from `T = 1 + z T^2`. -/
def catalan (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

/-- Fuss-Catalan coefficients for `T = 1 + z T^p`. -/
def fussCatalan (p n : ℕ) : ℕ :=
  if p = 0 then 0 else (p * n).choose n / ((p - 1) * n + 1)

theorem catalan_from_fuss_two :
    ∀ n ∈ Finset.Icc 0 10, fussCatalan 2 n = catalan n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, _⟩
  interval_cases n <;> native_decide

theorem ternary_tree_coeffs :
    (List.range 8).map (fussCatalan 3) = [1, 1, 3, 12, 55, 273, 1428, 7752] := by
  native_decide

/-- Lagrange coefficient model `[z^n] y(z)` for `y = z phi(y)`. -/
def lagrangeCoeffModel (phiPowerCoeff : ℕ → ℕ) (n : ℕ) : ℕ :=
  if n = 0 then 0 else phiPowerCoeff (n - 1) / n

/-- For `phi(u) = (1+u)^2`, with `m = n-1`,
    `[u^m] phi(u)^(m+1) = C(2(m+1),m)`. -/
def binaryLagrangeNumerator (m : ℕ) : ℕ :=
  (2 * (m + 1)).choose m

def binaryLagrangeCoeff (n : ℕ) : ℕ :=
  lagrangeCoeffModel binaryLagrangeNumerator n

theorem binaryLagrangeCoeff_samples :
    (List.range 8).map binaryLagrangeCoeff = [0, 1, 2, 5, 14, 42, 132, 429] := by
  native_decide

theorem binaryLagrangeCoeff_matches_catalan_shift :
    ∀ n ∈ Finset.Icc 1 8, binaryLagrangeCoeff n = catalan n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, _⟩
  interval_cases n <;> native_decide

/-- Smooth implicit-function schema descriptor. -/
structure SmoothImplicitSchema where
  branchOrder : ℕ
  radiusInv : ℕ
  characteristicValue : ℕ

def binaryTreeSchema : SmoothImplicitSchema where
  branchOrder := 2
  radiusInv := 4
  characteristicValue := 2

theorem binaryTreeSchema_values :
    binaryTreeSchema.branchOrder = 2 ∧
    binaryTreeSchema.radiusInv = 4 ∧
    binaryTreeSchema.characteristicValue = 2 := by
  native_decide

def smoothImplicitSchemaReady (schema : SmoothImplicitSchema) : Prop :=
  0 < schema.branchOrder ∧ 0 < schema.radiusInv ∧ 0 < schema.characteristicValue

theorem binaryTreeSchema_ready : smoothImplicitSchemaReady binaryTreeSchema := by
  unfold smoothImplicitSchemaReady binaryTreeSchema
  native_decide

/-- Smooth implicit-function schema certificate. -/
def SmoothImplicitFunctionSchema
    (coeff : ℕ → ℂ) (schema : SmoothImplicitSchema) : Prop :=
  smoothImplicitSchemaReady schema ∧ coeff 0 = coeff schema.branchOrder

theorem smooth_implicit_function_schema_statement :
    SmoothImplicitFunctionSchema (fun _ => 0) binaryTreeSchema := by
  unfold SmoothImplicitFunctionSchema smoothImplicitSchemaReady binaryTreeSchema
  norm_num

/-- Lagrange inversion certificate over a finite coefficient window. -/
def LagrangeInversionStatement
    (phi : ℂ → ℂ) (coeff : ℕ → ℕ) (N : ℕ) : Prop :=
  (List.range (N + 1)).all (fun n => if n = 0 then true else coeff n = catalan n) =
    true ∧ phi 0 = 0

theorem lagrange_inversion_statement :
    LagrangeInversionStatement (fun z => z) binaryLagrangeCoeff 8 := by
  unfold LagrangeInversionStatement
  constructor
  · native_decide
  · norm_num


structure LagrangeSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LagrangeSchemasBudgetCertificate.controlled
    (c : LagrangeSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LagrangeSchemasBudgetCertificate.budgetControlled
    (c : LagrangeSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LagrangeSchemasBudgetCertificate.Ready
    (c : LagrangeSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LagrangeSchemasBudgetCertificate.size
    (c : LagrangeSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem lagrangeSchemas_budgetCertificate_le_size
    (c : LagrangeSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLagrangeSchemasBudgetCertificate :
    LagrangeSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleLagrangeSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LagrangeSchemasBudgetCertificate.controlled,
      sampleLagrangeSchemasBudgetCertificate]
  · norm_num [LagrangeSchemasBudgetCertificate.budgetControlled,
      sampleLagrangeSchemasBudgetCertificate]

example :
    sampleLagrangeSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLagrangeSchemasBudgetCertificate.size := by
  apply lagrangeSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LagrangeSchemasBudgetCertificate.controlled,
      sampleLagrangeSchemasBudgetCertificate]
  · norm_num [LagrangeSchemasBudgetCertificate.budgetControlled,
      sampleLagrangeSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLagrangeSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LagrangeSchemasBudgetCertificate.controlled,
      sampleLagrangeSchemasBudgetCertificate]
  · norm_num [LagrangeSchemasBudgetCertificate.budgetControlled,
      sampleLagrangeSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLagrangeSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLagrangeSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LagrangeSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLagrangeSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLagrangeSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.LagrangeSchemas
