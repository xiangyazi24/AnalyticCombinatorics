import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Sets and the exp-log schema
-/

namespace AnalyticCombinatorics.PartB.Ch7.SetsAndExpLogSchema

def expLogSetProxy (components atoms : ℕ) : ℕ :=
  components + atoms

theorem expLogSetProxy_samples :
    expLogSetProxy 3 5 = 8 ∧ expLogSetProxy 0 4 = 4 := by
  native_decide

/-- Set construction table for assemblies with component counts by size. -/
def finiteSetConstruction (component : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + component n) 0

theorem finiteSetConstruction_zero (component : ℕ → ℕ) :
    finiteSetConstruction component 0 = component 0 := by
  simp [finiteSetConstruction]

/-- Exp-log schema envelope: components contribute additively in log scale. -/
def expLogEnvelope (componentBound atomBound n : ℕ) : ℕ :=
  (componentBound + atomBound) * (n + 1)

theorem expLogEnvelope_pos
    {componentBound atomBound : ℕ}
    (h : 0 < componentBound + atomBound) (n : ℕ) :
    0 < expLogEnvelope componentBound atomBound n := by
  unfold expLogEnvelope
  exact Nat.mul_pos h (Nat.succ_pos n)

def setSchemaReady (componentBound atomBound : ℕ) : Prop :=
  0 < componentBound + atomBound

theorem setSchemaReady_sample :
    setSchemaReady 2 3 := by
  norm_num [setSchemaReady]

def setConstructionEnvelopeCheck
    (component : ℕ → ℕ) (componentBound atomBound N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    component n ≤ expLogEnvelope componentBound atomBound n

theorem setConstructionEnvelopeCheck_const_one :
    setConstructionEnvelopeCheck (fun _ => 1) 1 0 8 = true := by
  unfold setConstructionEnvelopeCheck expLogEnvelope
  native_decide

example : finiteSetConstruction (fun n => n) 4 = 10 := by
  unfold finiteSetConstruction
  native_decide

example : expLogEnvelope 2 3 4 = 25 := by
  unfold expLogEnvelope
  native_decide

structure BudgetCertificate where
  setWindow : ℕ
  expLogWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.setWindow ∧ c.expLogWindow ≤ c.setWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.setWindow + c.expLogWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.setWindow + c.expLogWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { setWindow := 5, expLogWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.SetsAndExpLogSchema
