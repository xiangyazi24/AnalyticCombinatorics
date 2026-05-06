import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Schwarz reflection bookkeeping models.

The finite schema records boundary reality, symmetry, and extension budgets.
-/

namespace AnalyticCombinatorics.AppB.SchwarzReflectionModels

structure ReflectionDatum where
  boundaryReal : Prop
  symmetricDomain : Prop
  extensionBudget : ℕ
deriving Repr

def positiveExtensionBudget (d : ReflectionDatum) : Prop :=
  0 < d.extensionBudget

def reflectionReady (d : ReflectionDatum) : Prop :=
  d.boundaryReal ∧ d.symmetricDomain ∧ positiveExtensionBudget d

def reflectedBudget (d : ReflectionDatum) : ℕ :=
  d.extensionBudget + 1

theorem reflectionReady.symmetric {d : ReflectionDatum}
    (h : reflectionReady d) :
    d.symmetricDomain := h.2.1

theorem reflectedBudget_positive (d : ReflectionDatum) :
    0 < reflectedBudget d := by
  unfold reflectedBudget
  omega

def sampleReflection : ReflectionDatum :=
  { boundaryReal := ∀ k : Fin 4, k.val < 4
    symmetricDomain := ∀ k : Fin 4, k.val < 4
    extensionBudget := 3 }

example : reflectionReady sampleReflection := by
  unfold reflectionReady positiveExtensionBudget sampleReflection
  constructor
  · intro k
    exact k.isLt
  · constructor
    · intro k
      exact k.isLt
    · norm_num

example : reflectedBudget sampleReflection = 4 := by
  native_decide

/-- Prefix budget of reflected extensions over a finite sample list. -/
def reflectedBudgetPrefix (data : List ReflectionDatum) : ℕ :=
  data.foldl (fun total d => total + reflectedBudget d) 0

def trivialReflection : ReflectionDatum :=
  { boundaryReal := True
    symmetricDomain := True
    extensionBudget := 2 }

theorem reflectedBudgetPrefix_sampleWindow :
    reflectedBudgetPrefix
      [sampleReflection, trivialReflection] = 7 := by
  unfold reflectedBudgetPrefix reflectedBudget sampleReflection trivialReflection
  native_decide


structure SchwarzReflectionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SchwarzReflectionModelsBudgetCertificate.controlled
    (c : SchwarzReflectionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SchwarzReflectionModelsBudgetCertificate.budgetControlled
    (c : SchwarzReflectionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SchwarzReflectionModelsBudgetCertificate.Ready
    (c : SchwarzReflectionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SchwarzReflectionModelsBudgetCertificate.size
    (c : SchwarzReflectionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem schwarzReflectionModels_budgetCertificate_le_size
    (c : SchwarzReflectionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSchwarzReflectionModelsBudgetCertificate :
    SchwarzReflectionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSchwarzReflectionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [SchwarzReflectionModelsBudgetCertificate.controlled,
      sampleSchwarzReflectionModelsBudgetCertificate]
  · norm_num [SchwarzReflectionModelsBudgetCertificate.budgetControlled,
      sampleSchwarzReflectionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSchwarzReflectionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleSchwarzReflectionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSchwarzReflectionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [SchwarzReflectionModelsBudgetCertificate.controlled,
      sampleSchwarzReflectionModelsBudgetCertificate]
  · norm_num [SchwarzReflectionModelsBudgetCertificate.budgetControlled,
      sampleSchwarzReflectionModelsBudgetCertificate]

example :
    sampleSchwarzReflectionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleSchwarzReflectionModelsBudgetCertificate.size := by
  apply schwarzReflectionModels_budgetCertificate_le_size
  constructor
  · norm_num [SchwarzReflectionModelsBudgetCertificate.controlled,
      sampleSchwarzReflectionModelsBudgetCertificate]
  · norm_num [SchwarzReflectionModelsBudgetCertificate.budgetControlled,
      sampleSchwarzReflectionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SchwarzReflectionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSchwarzReflectionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSchwarzReflectionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.SchwarzReflectionModels
