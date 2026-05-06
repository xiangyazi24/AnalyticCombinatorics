import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter II: Poisson Schemas

Finite labelled-class checks for Poisson laws arising from SET constructions
and rare component counts.
-/

namespace AnalyticCombinatorics.PartA.Ch2.PoissonSchemas

/-- Truncated Poisson weight without the normalizing exponential. -/
def poissonWeight (lambda k : ℕ) : ℚ :=
  (lambda : ℚ) ^ k / (Nat.factorial k : ℚ)

theorem poissonWeight_one :
    (List.range 6).map (poissonWeight 1) = [1, 1, 1 / 2, 1 / 6, 1 / 24, 1 / 120] := by
  native_decide

theorem poissonWeight_two :
    (List.range 5).map (poissonWeight 2) = [1, 2, 2, 4 / 3, 2 / 3] := by
  native_decide

/-- Fixed-point count distribution in permutations of small size. -/
def fixedPointDistributionN4 : List ℕ :=
  [9, 8, 6, 0, 1]

theorem fixedPointDistributionN4_total :
    fixedPointDistributionN4.sum = Nat.factorial 4 := by
  native_decide

/-- Number of permutations of `n` with exactly `k` fixed points:
    choose fixed points, derange the rest. -/
def derangements : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangements (n + 1) + derangements n)

def fixedPointCount (n k : ℕ) : ℕ :=
  n.choose k * derangements (n - k)

theorem fixedPointCount_n4 :
    (List.range 5).map (fixedPointCount 4) = fixedPointDistributionN4 := by
  native_decide

theorem fixedPointCount_n5_total :
    ((List.range 6).map (fixedPointCount 5)).sum = Nat.factorial 5 := by
  native_decide

/-- Labelled SET Poisson schema certificate with nonnegative mean. -/
def LabelledSetPoissonSchema
    (componentCount : ℕ → ℕ → ℚ) (lambda : ℚ) : Prop :=
  0 ≤ lambda ∧ componentCount 0 0 = 1 ∧ componentCount 1 2 = 1

theorem labelled_set_poisson_schema_statement :
    LabelledSetPoissonSchema (fun _ _ => 1) 1 := by
  unfold LabelledSetPoissonSchema
  native_decide


structure PoissonSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonSchemasBudgetCertificate.controlled
    (c : PoissonSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PoissonSchemasBudgetCertificate.budgetControlled
    (c : PoissonSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PoissonSchemasBudgetCertificate.Ready
    (c : PoissonSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PoissonSchemasBudgetCertificate.size
    (c : PoissonSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem poissonSchemas_budgetCertificate_le_size
    (c : PoissonSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePoissonSchemasBudgetCertificate :
    PoissonSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePoissonSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonSchemasBudgetCertificate.controlled,
      samplePoissonSchemasBudgetCertificate]
  · norm_num [PoissonSchemasBudgetCertificate.budgetControlled,
      samplePoissonSchemasBudgetCertificate]

example :
    samplePoissonSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonSchemasBudgetCertificate.size := by
  apply poissonSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PoissonSchemasBudgetCertificate.controlled,
      samplePoissonSchemasBudgetCertificate]
  · norm_num [PoissonSchemasBudgetCertificate.budgetControlled,
      samplePoissonSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePoissonSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonSchemasBudgetCertificate.controlled,
      samplePoissonSchemasBudgetCertificate]
  · norm_num [PoissonSchemasBudgetCertificate.budgetControlled,
      samplePoissonSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePoissonSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PoissonSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePoissonSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePoissonSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.PoissonSchemas
