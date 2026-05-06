import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Admissible constructions and specifications
-/

namespace AnalyticCombinatorics.PartA.Ch1.AdmissibleConstructionsAndSpecifications

/-- Finite specification node count for a symbolic construction tree. -/
structure SpecificationSize where
  atoms : ℕ
  sums : ℕ
  products : ℕ
  sequences : ℕ
deriving DecidableEq, Repr

def SpecificationSize.total (s : SpecificationSize) : ℕ :=
  s.atoms + s.sums + s.products + s.sequences

def SpecificationSize.ready (s : SpecificationSize) : Prop :=
  0 < s.atoms ∧ s.sums + s.products + s.sequences ≤ s.total

theorem specificationSize_total_ge_atoms (s : SpecificationSize) :
    s.atoms ≤ s.total := by
  unfold SpecificationSize.total
  omega

/-- Sequence construction coefficients for a constant atom class. -/
def sequenceOfAtomsCoeff (_n : ℕ) : ℕ :=
  1

theorem sequenceOfAtomsCoeff_eq_one (n : ℕ) :
    sequenceOfAtomsCoeff n = 1 := rfl

def productConstructionCoeff (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + a k * b (n - k)) 0

theorem productConstructionCoeff_atom_sequence :
    productConstructionCoeff (fun n => if n = 1 then 1 else 0)
      sequenceOfAtomsCoeff 4 = 1 := by
  unfold productConstructionCoeff sequenceOfAtomsCoeff
  native_decide

structure BudgetCertificate where
  constructionWindow : ℕ
  specificationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.constructionWindow ∧
    c.specificationWindow ≤ c.constructionWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.constructionWindow + c.specificationWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.constructionWindow + c.specificationWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { constructionWindow := 5, specificationWindow := 6,
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

end AnalyticCombinatorics.PartA.Ch1.AdmissibleConstructionsAndSpecifications
