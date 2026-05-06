import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Additional constructions
-/

namespace AnalyticCombinatorics.PartA.Ch2.AdditionalConstructions

/-- Labelled product: choose the labels of the left component, then choose both structures. -/
def labelledProductCount (n k left right : ℕ) : ℕ :=
  Nat.choose n k * left * right

theorem labelledProductCount_sample :
    labelledProductCount 5 2 3 4 = 120 := by
  native_decide

/-- Labelled set construction from component counts on a finite list of block sizes. -/
def labelledSetPrefix (weights : List ℕ) : ℕ :=
  weights.foldl (fun acc w => acc + w) 0

theorem labelledSetPrefix_nil :
    labelledSetPrefix [] = 0 := by
  rfl

theorem labelledSetPrefix_sample :
    labelledSetPrefix [1, 3, 7, 15] = 26 := by
  native_decide

/-- A finite labelled cycle model: `(n - 1)!` cyclic orders on `n` labels. -/
def labelledCycleOrderCount (n : ℕ) : ℕ :=
  Nat.factorial (n - 1)

theorem labelledCycleOrderCount_four :
    labelledCycleOrderCount 4 = 6 := by
  native_decide

theorem labelledCycleOrderCount_six :
    labelledCycleOrderCount 6 = 120 := by
  native_decide

structure BudgetCertificate where
  constructionWindow : ℕ
  labelledWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.constructionWindow ∧
    c.labelledWindow ≤ c.constructionWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.constructionWindow + c.labelledWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.constructionWindow + c.labelledWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { constructionWindow := 5, labelledWindow := 6,
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

end AnalyticCombinatorics.PartA.Ch2.AdditionalConstructions
