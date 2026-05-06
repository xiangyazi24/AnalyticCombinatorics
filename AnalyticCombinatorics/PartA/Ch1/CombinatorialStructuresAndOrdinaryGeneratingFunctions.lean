import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Combinatorial structures and ordinary generating functions
-/

namespace AnalyticCombinatorics.PartA.Ch1.CombinatorialStructuresAndOrdinaryGeneratingFunctions

/-- Ordinary generating function coefficient extraction as a sequence lookup. -/
def ogfCoeff (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  a n

theorem ogfCoeff_eq (a : ℕ → ℕ) (n : ℕ) :
    ogfCoeff a n = a n := rfl

/-- Ordinary product construction: Cauchy convolution of coefficients. -/
def ogfProductCoeff (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + a k * b (n - k)) 0

theorem ogfProductCoeff_zero (a b : ℕ → ℕ) :
    ogfProductCoeff a b 0 = a 0 * b 0 := by
  simp [ogfProductCoeff]

theorem ogfProductCoeff_const_one_samples :
    ogfProductCoeff (fun _ => 1) (fun _ => 1) 0 = 1 ∧
      ogfProductCoeff (fun _ => 1) (fun _ => 1) 3 = 4 := by
  native_decide

/-- Ordinary sum construction: disjoint union adds coefficients. -/
def ogfSumCoeff (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  a n + b n

theorem ogfSumCoeff_comm (a b : ℕ → ℕ) (n : ℕ) :
    ogfSumCoeff a b n = ogfSumCoeff b a n := by
  simp [ogfSumCoeff, Nat.add_comm]

structure BudgetCertificate where
  structureWindow : ℕ
  ogfWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.structureWindow ∧ c.ogfWindow ≤ c.structureWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.structureWindow + c.ogfWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.structureWindow + c.ogfWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { structureWindow := 5, ogfWindow := 6, certificateBudgetWindow := 12,
    slack := 1 }

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

end AnalyticCombinatorics.PartA.Ch1.CombinatorialStructuresAndOrdinaryGeneratingFunctions
