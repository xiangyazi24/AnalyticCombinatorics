import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Combinatorial class bookkeeping.
-/

namespace AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

structure ClassProfile where
  objectCount : ℕ
  sizeBound : ℕ
  constructionSlack : ℕ
deriving DecidableEq, Repr

def classProfileReady (p : ClassProfile) : Prop :=
  0 < p.objectCount ∧ p.sizeBound ≤ p.objectCount + p.constructionSlack

def classProfileBudget (p : ClassProfile) : ℕ :=
  p.objectCount + p.sizeBound + p.constructionSlack

theorem sizeBound_le_budget (p : ClassProfile) :
    p.sizeBound ≤ classProfileBudget p := by
  unfold classProfileBudget
  omega

def sampleClassProfile : ClassProfile :=
  { objectCount := 8, sizeBound := 10, constructionSlack := 3 }

example : classProfileReady sampleClassProfile := by
  norm_num [classProfileReady, sampleClassProfile]

example : classProfileBudget sampleClassProfile = 21 := by native_decide

inductive ClassConstructor where
  | atom
  | epsilon
  | disjointUnion
  | cartesianProduct
  | sequence
deriving DecidableEq, Repr

def constructorRank : ClassConstructor → ℕ
  | .atom => 1
  | .epsilon => 0
  | .disjointUnion => 2
  | .cartesianProduct => 2
  | .sequence => 1

structure ClassWindow where
  constructor : ClassConstructor
  size : ℕ
  coefficient : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ClassWindow.rankBudget (w : ClassWindow) : ℕ :=
  constructorRank w.constructor + w.slack

def ClassWindow.coefficientControlled (w : ClassWindow) : Prop :=
  w.coefficient ≤ w.size + w.rankBudget

def ClassWindow.nonempty (w : ClassWindow) : Prop :=
  0 < w.coefficient

def ClassWindow.certificate (w : ClassWindow) : ℕ :=
  w.size + w.coefficient + w.rankBudget

theorem size_le_certificate (w : ClassWindow) :
    w.size ≤ w.certificate := by
  unfold ClassWindow.certificate
  omega

def sampleClassWindow : ClassWindow :=
  { constructor := ClassConstructor.cartesianProduct, size := 5, coefficient := 7, slack := 1 }

example : sampleClassWindow.coefficientControlled := by
  norm_num [sampleClassWindow, ClassWindow.coefficientControlled, ClassWindow.rankBudget,
    constructorRank]

example : sampleClassWindow.nonempty := by
  norm_num [sampleClassWindow, ClassWindow.nonempty]


structure CombinatorialClassBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CombinatorialClassBudgetCertificate.controlled
    (c : CombinatorialClassBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CombinatorialClassBudgetCertificate.budgetControlled
    (c : CombinatorialClassBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CombinatorialClassBudgetCertificate.Ready
    (c : CombinatorialClassBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CombinatorialClassBudgetCertificate.size
    (c : CombinatorialClassBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem combinatorialClass_budgetCertificate_le_size
    (c : CombinatorialClassBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCombinatorialClassBudgetCertificate :
    CombinatorialClassBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCombinatorialClassBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatorialClassBudgetCertificate.controlled,
      sampleCombinatorialClassBudgetCertificate]
  · norm_num [CombinatorialClassBudgetCertificate.budgetControlled,
      sampleCombinatorialClassBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCombinatorialClassBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatorialClassBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCombinatorialClassBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatorialClassBudgetCertificate.controlled,
      sampleCombinatorialClassBudgetCertificate]
  · norm_num [CombinatorialClassBudgetCertificate.budgetControlled,
      sampleCombinatorialClassBudgetCertificate]

example :
    sampleCombinatorialClassBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatorialClassBudgetCertificate.size := by
  apply combinatorialClass_budgetCertificate_le_size
  constructor
  · norm_num [CombinatorialClassBudgetCertificate.controlled,
      sampleCombinatorialClassBudgetCertificate]
  · norm_num [CombinatorialClassBudgetCertificate.budgetControlled,
      sampleCombinatorialClassBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CombinatorialClassBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCombinatorialClassBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCombinatorialClassBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
