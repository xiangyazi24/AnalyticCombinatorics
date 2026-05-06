import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Poissonization
-/

namespace AnalyticCombinatorics.Asymptotics.Poissonization

def poissonWeightProxy (n k : ℕ) : ℕ :=
  n ^ k / Nat.factorial k

theorem poissonWeightProxy_zero_index (n : ℕ) :
    poissonWeightProxy n 0 = 1 := by
  simp [poissonWeightProxy]

theorem poissonWeightProxy_zero_parameter {k : ℕ} (hk : 0 < k) :
    poissonWeightProxy 0 k = 0 := by
  cases k with
  | zero =>
      cases hk
  | succ k =>
      simp [poissonWeightProxy]

theorem poissonWeightProxy_samples :
    poissonWeightProxy 2 0 = 1 ∧ poissonWeightProxy 2 2 = 2 := by
  native_decide

/-- Finite Poisson transform after dropping the common exponential factor. -/
def poissonTransformPrefix (a : ℕ → ℕ) (z N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total k => total + a k * poissonWeightProxy z k) 0

theorem poissonTransformPrefix_zero :
    poissonTransformPrefix (fun _ => 1) 0 4 = 1 := by
  unfold poissonTransformPrefix poissonWeightProxy
  native_decide

theorem poissonTransformPrefix_constant_samples :
    poissonTransformPrefix (fun _ => 1) 2 3 = 6 := by
  unfold poissonTransformPrefix poissonWeightProxy
  native_decide

structure BudgetCertificate where
  poissonWindow : ℕ
  transformWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.poissonWindow ∧ c.transformWindow ≤ c.poissonWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.poissonWindow + c.transformWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.poissonWindow + c.transformWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { poissonWindow := 5, transformWindow := 6,
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

example :
    budgetCertificateListReady
      [sampleBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.Asymptotics.Poissonization
