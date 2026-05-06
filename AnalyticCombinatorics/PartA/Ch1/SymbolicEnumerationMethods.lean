import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Symbolic enumeration methods.

Finite bookkeeping for class specifications, size maps, and coefficient
extraction windows in the symbolic method.
-/

namespace AnalyticCombinatorics.PartA.Ch1.SymbolicEnumerationMethods

/-- Atomic class coefficient: one object of size one. -/
def atomCoeff : ℕ → ℕ
  | 1 => 1
  | _ => 0

/-- Sequence construction over one atom: one word of each size. -/
def sequenceOfAtomsCoeff (_n : ℕ) : ℕ :=
  1

/-- Finite symbolic transfer check from atoms to sequences. -/
def symbolicSequenceCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => atomCoeff n ≤ sequenceOfAtomsCoeff n

theorem symbolicSequence_window :
    symbolicSequenceCheck 16 = true := by
  unfold symbolicSequenceCheck atomCoeff sequenceOfAtomsCoeff
  native_decide

structure SymbolicEnumerationData where
  atomTypes : ℕ
  constructionCount : ℕ
  coefficientDepth : ℕ
  enumerationSlack : ℕ
deriving DecidableEq, Repr

def hasAtoms (d : SymbolicEnumerationData) : Prop :=
  0 < d.atomTypes

def coefficientDepthControlled (d : SymbolicEnumerationData) : Prop :=
  d.coefficientDepth ≤ d.atomTypes * (d.constructionCount + 1) + d.enumerationSlack

def symbolicEnumerationReady (d : SymbolicEnumerationData) : Prop :=
  hasAtoms d ∧ coefficientDepthControlled d

def symbolicEnumerationBudget (d : SymbolicEnumerationData) : ℕ :=
  d.atomTypes + d.constructionCount + d.coefficientDepth + d.enumerationSlack

theorem coefficientDepth_le_budget
    (d : SymbolicEnumerationData) :
    d.coefficientDepth ≤ symbolicEnumerationBudget d + d.atomTypes * d.constructionCount := by
  unfold symbolicEnumerationBudget
  omega

def sampleSymbolicEnumerationData : SymbolicEnumerationData :=
  { atomTypes := 2
    constructionCount := 4
    coefficientDepth := 9
    enumerationSlack := 1 }

example : symbolicEnumerationReady sampleSymbolicEnumerationData := by
  norm_num [symbolicEnumerationReady, hasAtoms,
    coefficientDepthControlled, sampleSymbolicEnumerationData]

structure SymbolicEnumerationMethodsBudgetCertificate where
  atomWindow : ℕ
  constructionWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SymbolicEnumerationMethodsBudgetCertificate.controlled
    (c : SymbolicEnumerationMethodsBudgetCertificate) : Prop :=
  0 < c.atomWindow ∧
    c.coefficientWindow ≤ c.atomWindow * (c.constructionWindow + 1) + c.slack

def SymbolicEnumerationMethodsBudgetCertificate.budgetControlled
    (c : SymbolicEnumerationMethodsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.atomWindow + c.constructionWindow + c.coefficientWindow + c.slack

def SymbolicEnumerationMethodsBudgetCertificate.Ready
    (c : SymbolicEnumerationMethodsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SymbolicEnumerationMethodsBudgetCertificate.size
    (c : SymbolicEnumerationMethodsBudgetCertificate) : ℕ :=
  c.atomWindow + c.constructionWindow + c.coefficientWindow + c.slack

theorem symbolicEnumerationMethods_budgetCertificate_le_size
    (c : SymbolicEnumerationMethodsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSymbolicEnumerationMethodsBudgetCertificate :
    SymbolicEnumerationMethodsBudgetCertificate :=
  { atomWindow := 2
    constructionWindow := 4
    coefficientWindow := 9
    certificateBudgetWindow := 16
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSymbolicEnumerationMethodsBudgetCertificate.Ready := by
  constructor
  · norm_num [SymbolicEnumerationMethodsBudgetCertificate.controlled,
      sampleSymbolicEnumerationMethodsBudgetCertificate]
  · norm_num [SymbolicEnumerationMethodsBudgetCertificate.budgetControlled,
      sampleSymbolicEnumerationMethodsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSymbolicEnumerationMethodsBudgetCertificate.certificateBudgetWindow ≤
      sampleSymbolicEnumerationMethodsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSymbolicEnumerationMethodsBudgetCertificate.Ready := by
  constructor
  · norm_num [SymbolicEnumerationMethodsBudgetCertificate.controlled,
      sampleSymbolicEnumerationMethodsBudgetCertificate]
  · norm_num [SymbolicEnumerationMethodsBudgetCertificate.budgetControlled,
      sampleSymbolicEnumerationMethodsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SymbolicEnumerationMethodsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSymbolicEnumerationMethodsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSymbolicEnumerationMethodsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.SymbolicEnumerationMethods
