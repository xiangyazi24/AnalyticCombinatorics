import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite multiset models represented by lists.

The file keeps small multiplicity calculations executable without relying on
project-local multiset infrastructure.
-/

namespace AnalyticCombinatorics.AppA.FiniteMultisetModels

def multiplicity (x : ℕ) (xs : List ℕ) : ℕ :=
  xs.filter (fun y => y == x) |>.length

def supportSize (xs : List ℕ) : ℕ :=
  xs.eraseDups.length

def totalMultiplicity (xs : List ℕ) : ℕ :=
  xs.length

def multiplicityBounded (xs : List ℕ) (bound : ℕ) : Prop :=
  ∀ x ∈ xs, multiplicity x xs ≤ bound

theorem multiplicity_nil (x : ℕ) :
    multiplicity x [] = 0 := by
  rfl

theorem totalMultiplicity_cons (x : ℕ) (xs : List ℕ) :
    totalMultiplicity (x :: xs) = totalMultiplicity xs + 1 := by
  simp [totalMultiplicity]

theorem supportSize_nil :
    supportSize [] = 0 := by
  rfl

def sampleMultiset : List ℕ :=
  [2, 3, 2, 5, 3, 2]

example : multiplicity 2 sampleMultiset = 3 := by
  native_decide

example : supportSize sampleMultiset = 3 := by
  native_decide

example : totalMultiplicity sampleMultiset = 6 := by
  native_decide

structure MultisetWindow where
  total : ℕ
  support : ℕ
  maxMultiplicity : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultisetWindow.supportControlled (w : MultisetWindow) : Prop :=
  w.support ≤ w.total + w.slack

def MultisetWindow.multiplicityControlled (w : MultisetWindow) : Prop :=
  w.total ≤ w.support * w.maxMultiplicity + w.slack

def MultisetWindow.ready (w : MultisetWindow) : Prop :=
  w.supportControlled ∧ w.multiplicityControlled

def MultisetWindow.certificate (w : MultisetWindow) : ℕ :=
  w.total + w.support + w.maxMultiplicity + w.slack

theorem support_le_certificate (w : MultisetWindow) :
    w.support ≤ w.certificate := by
  unfold MultisetWindow.certificate
  omega

def sampleMultisetWindow : MultisetWindow :=
  { total := 6, support := 3, maxMultiplicity := 3, slack := 0 }

example : sampleMultisetWindow.ready := by
  norm_num [sampleMultisetWindow, MultisetWindow.ready,
    MultisetWindow.supportControlled, MultisetWindow.multiplicityControlled]


structure FiniteMultisetModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteMultisetModelsBudgetCertificate.controlled
    (c : FiniteMultisetModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteMultisetModelsBudgetCertificate.budgetControlled
    (c : FiniteMultisetModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteMultisetModelsBudgetCertificate.Ready
    (c : FiniteMultisetModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteMultisetModelsBudgetCertificate.size
    (c : FiniteMultisetModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteMultisetModels_budgetCertificate_le_size
    (c : FiniteMultisetModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteMultisetModelsBudgetCertificate :
    FiniteMultisetModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteMultisetModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteMultisetModelsBudgetCertificate.controlled,
      sampleFiniteMultisetModelsBudgetCertificate]
  · norm_num [FiniteMultisetModelsBudgetCertificate.budgetControlled,
      sampleFiniteMultisetModelsBudgetCertificate]

example :
    sampleFiniteMultisetModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteMultisetModelsBudgetCertificate.size := by
  apply finiteMultisetModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteMultisetModelsBudgetCertificate.controlled,
      sampleFiniteMultisetModelsBudgetCertificate]
  · norm_num [FiniteMultisetModelsBudgetCertificate.budgetControlled,
      sampleFiniteMultisetModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteMultisetModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteMultisetModelsBudgetCertificate.controlled,
      sampleFiniteMultisetModelsBudgetCertificate]
  · norm_num [FiniteMultisetModelsBudgetCertificate.budgetControlled,
      sampleFiniteMultisetModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteMultisetModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteMultisetModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteMultisetModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteMultisetModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteMultisetModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteMultisetModels
