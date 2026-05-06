import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Surjection schemas.
-/

namespace AnalyticCombinatorics.PartA.Ch2.Surjections

structure SurjectionWindow where
  domainSize : ℕ
  codomainSize : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def possibleSurjectionWindow (w : SurjectionWindow) : Prop :=
  w.codomainSize ≤ w.domainSize

def nonemptyCodomain (w : SurjectionWindow) : Prop :=
  0 < w.codomainSize

def surjectionWindowReady (w : SurjectionWindow) : Prop :=
  nonemptyCodomain w ∧ possibleSurjectionWindow w

def surjectionWindowBudget (w : SurjectionWindow) : ℕ :=
  w.domainSize + w.codomainSize + w.slack

def stirlingSecond : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k

def surjectionCount (n k : ℕ) : ℕ :=
  k.factorial * stirlingSecond n k

theorem surjectionWindowReady.certificate {w : SurjectionWindow}
    (h : surjectionWindowReady w) :
    nonemptyCodomain w ∧ possibleSurjectionWindow w ∧
      w.codomainSize ≤ surjectionWindowBudget w := by
  rcases h with ⟨hcodomain, hpossible⟩
  refine ⟨hcodomain, hpossible, ?_⟩
  unfold surjectionWindowBudget
  omega

def sampleSurjectionWindow : SurjectionWindow :=
  { domainSize := 5, codomainSize := 3, slack := 1 }

example : surjectionWindowReady sampleSurjectionWindow := by
  norm_num [surjectionWindowReady, nonemptyCodomain, possibleSurjectionWindow,
    sampleSurjectionWindow]

example : surjectionCount 3 2 = 6 := by native_decide
example : surjectionCount 4 2 = 14 := by native_decide
example : surjectionCount 5 3 = 150 := by native_decide
example : stirlingSecond 5 3 = 25 := by native_decide
example : surjectionWindowBudget sampleSurjectionWindow = 9 := by native_decide

theorem surjectionCount_self_upto_8 :
    (List.range 9).all
      (fun n => surjectionCount n n == n.factorial) = true := by
  native_decide


structure SurjectionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SurjectionsBudgetCertificate.controlled
    (c : SurjectionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SurjectionsBudgetCertificate.budgetControlled
    (c : SurjectionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SurjectionsBudgetCertificate.Ready
    (c : SurjectionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SurjectionsBudgetCertificate.size
    (c : SurjectionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem surjections_budgetCertificate_le_size
    (c : SurjectionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSurjectionsBudgetCertificate :
    SurjectionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSurjectionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SurjectionsBudgetCertificate.controlled,
      sampleSurjectionsBudgetCertificate]
  · norm_num [SurjectionsBudgetCertificate.budgetControlled,
      sampleSurjectionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSurjectionsBudgetCertificate.certificateBudgetWindow ≤
      sampleSurjectionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSurjectionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SurjectionsBudgetCertificate.controlled,
      sampleSurjectionsBudgetCertificate]
  · norm_num [SurjectionsBudgetCertificate.budgetControlled,
      sampleSurjectionsBudgetCertificate]

example :
    sampleSurjectionsBudgetCertificate.certificateBudgetWindow ≤
      sampleSurjectionsBudgetCertificate.size := by
  apply surjections_budgetCertificate_le_size
  constructor
  · norm_num [SurjectionsBudgetCertificate.controlled,
      sampleSurjectionsBudgetCertificate]
  · norm_num [SurjectionsBudgetCertificate.budgetControlled,
      sampleSurjectionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SurjectionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSurjectionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSurjectionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.Surjections
