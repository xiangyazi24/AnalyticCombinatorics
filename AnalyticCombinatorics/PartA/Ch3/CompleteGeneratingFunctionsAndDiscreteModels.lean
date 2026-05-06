import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Complete generating functions and discrete models
-/

namespace AnalyticCombinatorics.PartA.Ch3.CompleteGeneratingFunctionsAndDiscreteModels

/-- Complete generating function coefficient for a finite vector of marks. -/
def completeCoeff (table : List ℕ → ℕ) (marks : List ℕ) : ℕ :=
  table marks

def markWeight (marks : List ℕ) : ℕ :=
  marks.foldl (fun total k => total + k) 0

theorem markWeight_nil :
    markWeight [] = 0 := rfl

theorem markWeight_foldl_acc (ks : List ℕ) (acc : ℕ) :
    ks.foldl (fun total k => total + k) acc =
      acc + ks.foldl (fun total k => total + k) 0 := by
  induction ks generalizing acc with
  | nil =>
      simp
  | cons k ks ih =>
      simp only [List.foldl, zero_add]
      have hleft := ih (acc + k)
      have hright := ih k
      omega

theorem markWeight_cons (k : ℕ) (ks : List ℕ) :
    markWeight (k :: ks) = k + markWeight ks := by
  unfold markWeight
  simp only [List.foldl, zero_add]
  exact markWeight_foldl_acc ks k

/-- A discrete model is finite when all sampled mark weights stay bounded. -/
def finiteDiscreteModelReady (samples : List (List ℕ)) (bound : ℕ) : Bool :=
  samples.all fun marks => markWeight marks ≤ bound

theorem finiteDiscreteModelReady_sample :
    finiteDiscreteModelReady [[1, 0], [0, 2], [1, 1]] 2 = true := by
  unfold finiteDiscreteModelReady markWeight
  native_decide

structure BudgetCertificate where
  completeGFWindow : ℕ
  discreteModelWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.completeGFWindow ∧
    c.discreteModelWindow ≤ c.completeGFWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.completeGFWindow + c.discreteModelWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.completeGFWindow + c.discreteModelWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { completeGFWindow := 5, discreteModelWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

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

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

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

end AnalyticCombinatorics.PartA.Ch3.CompleteGeneratingFunctionsAndDiscreteModels
