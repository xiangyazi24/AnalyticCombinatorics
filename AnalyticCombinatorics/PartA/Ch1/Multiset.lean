import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multiset construction schemas.

The finite schema records multiplicity budgets and the standard
stars-and-bars count for multisets of fixed size.
-/

namespace AnalyticCombinatorics.PartA.Ch1.Multiset

def multisetCount (atomTypes size : ℕ) : ℕ :=
  if atomTypes = 0 then
    if size = 0 then 1 else 0
  else
    Nat.choose (atomTypes + size - 1) size

def multisetBudget (atoms multiplicity slack : ℕ) : ℕ :=
  atoms + multiplicity + slack

def multisetReady (atoms multiplicity slack : ℕ) : Prop :=
  0 < atoms ∧ multiplicity ≤ atoms + slack

structure MultisetWindow where
  atomTypes : ℕ
  totalMultiplicity : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def multisetWindowReady (w : MultisetWindow) : Prop :=
  multisetReady w.atomTypes w.totalMultiplicity w.slack

def multisetWindowBudget (w : MultisetWindow) : ℕ :=
  multisetBudget w.atomTypes w.totalMultiplicity w.slack

theorem multiplicity_le_budget (atoms multiplicity slack : ℕ) :
    multiplicity ≤ multisetBudget atoms multiplicity slack := by
  unfold multisetBudget
  omega

theorem multisetWindowReady.certificate {w : MultisetWindow}
    (h : multisetWindowReady w) :
    0 < w.atomTypes ∧ w.totalMultiplicity ≤ w.atomTypes + w.slack ∧
      w.totalMultiplicity ≤ multisetWindowBudget w := by
  rcases h with ⟨hatoms, hcontrolled⟩
  refine ⟨hatoms, hcontrolled, ?_⟩
  unfold multisetWindowBudget multisetBudget
  omega

def sampleMultisetWindow : MultisetWindow :=
  { atomTypes := 5, totalMultiplicity := 6, slack := 2 }

example : multisetReady 5 6 2 := by norm_num [multisetReady]
example : multisetBudget 5 6 2 = 13 := by native_decide
example : multisetWindowReady sampleMultisetWindow := by
  norm_num [multisetWindowReady, multisetReady, sampleMultisetWindow]
example : multisetWindowBudget sampleMultisetWindow = 13 := by native_decide
example : multisetCount 3 0 = 1 := by native_decide
example : multisetCount 3 2 = 6 := by native_decide
example : multisetCount 4 3 = 20 := by native_decide
example : multisetCount 0 2 = 0 := by native_decide


structure MultisetBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultisetBudgetCertificate.controlled
    (c : MultisetBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MultisetBudgetCertificate.budgetControlled
    (c : MultisetBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MultisetBudgetCertificate.Ready
    (c : MultisetBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultisetBudgetCertificate.size
    (c : MultisetBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem multiset_budgetCertificate_le_size
    (c : MultisetBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMultisetBudgetCertificate :
    MultisetBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMultisetBudgetCertificate.Ready := by
  constructor
  · norm_num [MultisetBudgetCertificate.controlled,
      sampleMultisetBudgetCertificate]
  · norm_num [MultisetBudgetCertificate.budgetControlled,
      sampleMultisetBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultisetBudgetCertificate.certificateBudgetWindow ≤
      sampleMultisetBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMultisetBudgetCertificate.Ready := by
  constructor
  · norm_num [MultisetBudgetCertificate.controlled,
      sampleMultisetBudgetCertificate]
  · norm_num [MultisetBudgetCertificate.budgetControlled,
      sampleMultisetBudgetCertificate]

example :
    sampleMultisetBudgetCertificate.certificateBudgetWindow ≤
      sampleMultisetBudgetCertificate.size := by
  apply multiset_budgetCertificate_le_size
  constructor
  · norm_num [MultisetBudgetCertificate.controlled,
      sampleMultisetBudgetCertificate]
  · norm_num [MultisetBudgetCertificate.budgetControlled,
      sampleMultisetBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MultisetBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultisetBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMultisetBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.Multiset
