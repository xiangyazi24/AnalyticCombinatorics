import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix A: Finite Set Systems

Finite family, incidence, and inclusion-exclusion models.
-/

namespace AnalyticCombinatorics.AppA.FiniteSetSystems

def incidenceCount (sets : List (List ℕ)) (x : ℕ) : ℕ :=
  sets.countP fun s => x ∈ s

theorem incidenceCount_samples :
    incidenceCount [[1, 2], [2, 3], [2]] 2 = 3 ∧
    incidenceCount [[1], [2], [3]] 2 = 1 := by
  native_decide

def unionSizeToy (sets : List (List ℕ)) : ℕ :=
  (sets.flatten.eraseDups).length

theorem unionSizeToy_samples :
    unionSizeToy [[1, 2], [2, 3], [3, 4]] = 4 := by
  native_decide

def intersectionNonempty (a b : List ℕ) : Bool :=
  a.any fun x => x ∈ b

theorem intersectionNonempty_samples :
    intersectionNonempty [1, 2] [3, 4] = false ∧
    intersectionNonempty [1, 2] [2, 4] = true := by
  native_decide

def pairwiseIntersecting (sets : List (List ℕ)) : Bool :=
  (List.range sets.length).all fun i =>
    (List.range sets.length).all fun j =>
      if i < j then intersectionNonempty (sets.getD i []) (sets.getD j []) else true

theorem pairwiseIntersecting_samples :
    pairwiseIntersecting [[1, 2], [2, 3], [1, 3]] = true ∧
    pairwiseIntersecting [[1], [2], [1, 2]] = false := by
  native_decide

def InclusionExclusionSetSystem
    (sets : List (List ℕ)) (count : ℕ) : Prop :=
  unionSizeToy sets = count

theorem inclusion_exclusion_set_system_statement :
    InclusionExclusionSetSystem [[1, 2], [2, 3], [3, 4]] 4 := by
  unfold InclusionExclusionSetSystem unionSizeToy
  native_decide

/-- Prefix incidence count over a finite universe window. -/
def incidencePrefix (sets : List (List ℕ)) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total x => total + incidenceCount sets x) 0

theorem incidencePrefix_window :
    incidencePrefix [[1, 2], [2, 3], [2]] 3 = 5 := by
  unfold incidencePrefix incidenceCount
  native_decide


structure FiniteSetSystemsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSetSystemsBudgetCertificate.controlled
    (c : FiniteSetSystemsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSetSystemsBudgetCertificate.budgetControlled
    (c : FiniteSetSystemsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSetSystemsBudgetCertificate.Ready
    (c : FiniteSetSystemsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSetSystemsBudgetCertificate.size
    (c : FiniteSetSystemsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSetSystems_budgetCertificate_le_size
    (c : FiniteSetSystemsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSetSystemsBudgetCertificate :
    FiniteSetSystemsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteSetSystemsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSetSystemsBudgetCertificate.controlled,
      sampleFiniteSetSystemsBudgetCertificate]
  · norm_num [FiniteSetSystemsBudgetCertificate.budgetControlled,
      sampleFiniteSetSystemsBudgetCertificate]

example :
    sampleFiniteSetSystemsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSetSystemsBudgetCertificate.size := by
  apply finiteSetSystems_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSetSystemsBudgetCertificate.controlled,
      sampleFiniteSetSystemsBudgetCertificate]
  · norm_num [FiniteSetSystemsBudgetCertificate.budgetControlled,
      sampleFiniteSetSystemsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteSetSystemsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSetSystemsBudgetCertificate.controlled,
      sampleFiniteSetSystemsBudgetCertificate]
  · norm_num [FiniteSetSystemsBudgetCertificate.budgetControlled,
      sampleFiniteSetSystemsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSetSystemsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSetSystemsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteSetSystemsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSetSystemsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSetSystemsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSetSystems
