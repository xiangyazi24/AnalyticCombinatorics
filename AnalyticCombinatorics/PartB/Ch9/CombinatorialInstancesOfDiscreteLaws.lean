import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Combinatorial instances of discrete laws
-/

namespace AnalyticCombinatorics.PartB.Ch9.CombinatorialInstancesOfDiscreteLaws

/-- Finite law table entry for a discrete combinatorial model. -/
structure DiscreteLawMass where
  parameterValue : ℕ
  multiplicity : ℕ
deriving DecidableEq, Repr

def discreteLawTotalMass (data : List DiscreteLawMass) : ℕ :=
  data.foldl (fun acc x => acc + x.multiplicity) 0

theorem discreteLawTotalMass_sample :
    discreteLawTotalMass
      [{ parameterValue := 0, multiplicity := 2 },
       { parameterValue := 1, multiplicity := 5 },
       { parameterValue := 2, multiplicity := 3 }] = 10 := by
  native_decide

def discreteLawFirstMoment (data : List DiscreteLawMass) : ℕ :=
  data.foldl (fun acc x => acc + x.parameterValue * x.multiplicity) 0

theorem discreteLawFirstMoment_sample :
    discreteLawFirstMoment
      [{ parameterValue := 0, multiplicity := 2 },
       { parameterValue := 1, multiplicity := 5 },
       { parameterValue := 2, multiplicity := 3 }] = 11 := by
  native_decide

structure DiscreteLawInstanceWindow where
  instanceWindow : ℕ
  lawWindow : ℕ
  verificationWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DiscreteLawInstanceWindow.ready (w : DiscreteLawInstanceWindow) : Prop :=
  0 < w.instanceWindow ∧
    w.verificationWindow ≤ w.instanceWindow + w.lawWindow + w.slack

def sampleDiscreteLawInstanceWindow : DiscreteLawInstanceWindow :=
  { instanceWindow := 4, lawWindow := 3,
    verificationWindow := 7, slack := 0 }

example : sampleDiscreteLawInstanceWindow.ready := by
  norm_num [DiscreteLawInstanceWindow.ready, sampleDiscreteLawInstanceWindow]

structure BudgetCertificate where
  instanceWindow : ℕ
  lawWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.instanceWindow ∧ c.lawWindow ≤ c.instanceWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.instanceWindow + c.lawWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.instanceWindow + c.lawWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { instanceWindow := 5, lawWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  have h : sampleBudgetCertificate.Ready := by
    constructor
    · norm_num [BudgetCertificate.controlled,
        sampleBudgetCertificate]
    · norm_num [BudgetCertificate.budgetControlled,
        sampleBudgetCertificate]
  exact h.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.CombinatorialInstancesOfDiscreteLaws
