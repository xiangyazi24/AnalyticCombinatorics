import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Unlabelled multiset schemas.

The finite record stores atom classes, multiplicity budget, and symmetry
slack.
-/

namespace AnalyticCombinatorics.PartA.Ch1.UnlabelledMultisetSchemas

structure UnlabelledMultisetData where
  atomClasses : ℕ
  multiplicityBudget : ℕ
  symmetrySlack : ℕ
deriving DecidableEq, Repr

def atomClassesPositive (d : UnlabelledMultisetData) : Prop :=
  0 < d.atomClasses

def multiplicityControlled (d : UnlabelledMultisetData) : Prop :=
  d.multiplicityBudget ≤ d.atomClasses + d.symmetrySlack

def unlabelledMultisetReady (d : UnlabelledMultisetData) : Prop :=
  atomClassesPositive d ∧ multiplicityControlled d

def unlabelledMultisetBudget (d : UnlabelledMultisetData) : ℕ :=
  d.atomClasses + d.multiplicityBudget + d.symmetrySlack

theorem unlabelledMultisetReady.atoms {d : UnlabelledMultisetData}
    (h : unlabelledMultisetReady d) :
    atomClassesPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem multiplicityBudget_le_unlabelledMultisetBudget
    (d : UnlabelledMultisetData) :
    d.multiplicityBudget ≤ unlabelledMultisetBudget d := by
  unfold unlabelledMultisetBudget
  omega

def sampleUnlabelledMultisetData : UnlabelledMultisetData :=
  { atomClasses := 6, multiplicityBudget := 8, symmetrySlack := 3 }

example : unlabelledMultisetReady sampleUnlabelledMultisetData := by
  norm_num [unlabelledMultisetReady, atomClassesPositive]
  norm_num [multiplicityControlled, sampleUnlabelledMultisetData]

example : unlabelledMultisetBudget sampleUnlabelledMultisetData = 17 := by
  native_decide

structure UnlabelledMultisetBudgetCertificate where
  atomClassWindow : ℕ
  multiplicityWindow : ℕ
  symmetrySlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UnlabelledMultisetBudgetCertificate.controlled
    (c : UnlabelledMultisetBudgetCertificate) : Prop :=
  0 < c.atomClassWindow ∧
    c.multiplicityWindow ≤ c.atomClassWindow + c.symmetrySlackWindow + c.slack

def UnlabelledMultisetBudgetCertificate.budgetControlled
    (c : UnlabelledMultisetBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.atomClassWindow + c.multiplicityWindow + c.symmetrySlackWindow + c.slack

def UnlabelledMultisetBudgetCertificate.Ready
    (c : UnlabelledMultisetBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UnlabelledMultisetBudgetCertificate.size
    (c : UnlabelledMultisetBudgetCertificate) : ℕ :=
  c.atomClassWindow + c.multiplicityWindow + c.symmetrySlackWindow + c.slack

theorem unlabelledMultiset_budgetCertificate_le_size
    (c : UnlabelledMultisetBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUnlabelledMultisetBudgetCertificate :
    UnlabelledMultisetBudgetCertificate :=
  { atomClassWindow := 6
    multiplicityWindow := 8
    symmetrySlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUnlabelledMultisetBudgetCertificate.Ready := by
  constructor
  · norm_num [UnlabelledMultisetBudgetCertificate.controlled,
      sampleUnlabelledMultisetBudgetCertificate]
  · norm_num [UnlabelledMultisetBudgetCertificate.budgetControlled,
      sampleUnlabelledMultisetBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUnlabelledMultisetBudgetCertificate.certificateBudgetWindow ≤
      sampleUnlabelledMultisetBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUnlabelledMultisetBudgetCertificate.Ready := by
  constructor
  · norm_num [UnlabelledMultisetBudgetCertificate.controlled,
      sampleUnlabelledMultisetBudgetCertificate]
  · norm_num [UnlabelledMultisetBudgetCertificate.budgetControlled,
      sampleUnlabelledMultisetBudgetCertificate]

example :
    sampleUnlabelledMultisetBudgetCertificate.certificateBudgetWindow ≤
      sampleUnlabelledMultisetBudgetCertificate.size := by
  apply unlabelledMultiset_budgetCertificate_le_size
  constructor
  · norm_num [UnlabelledMultisetBudgetCertificate.controlled,
      sampleUnlabelledMultisetBudgetCertificate]
  · norm_num [UnlabelledMultisetBudgetCertificate.budgetControlled,
      sampleUnlabelledMultisetBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UnlabelledMultisetBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleUnlabelledMultisetBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleUnlabelledMultisetBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.UnlabelledMultisetSchemas
