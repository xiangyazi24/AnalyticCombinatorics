import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Subsequence extraction schemas for compactness arguments.

The definitions track the arithmetic side of selecting increasing index
maps and preserving tightness hypotheses.
-/

namespace AnalyticCombinatorics.AppC.SubsequenceLimitSchemas

def strictlyIncreasing (f : ℕ → ℕ) : Prop :=
  ∀ n, f n < f (n + 1)

structure SubsequenceSchema where
  indexMap : ℕ → ℕ
  tightFamily : Prop
  limitIdentified : Prop

def compactnessReady (s : SubsequenceSchema) : Prop :=
  strictlyIncreasing s.indexMap ∧ s.tightFamily

def convergenceReady (s : SubsequenceSchema) : Prop :=
  compactnessReady s ∧ s.limitIdentified

theorem strictlyIncreasing_succ_le {f : ℕ → ℕ}
    (h : strictlyIncreasing f) (n : ℕ) :
    f n + 1 ≤ f (n + 1) := by
  exact Nat.succ_le_of_lt (h n)

theorem convergenceReady.compact {s : SubsequenceSchema}
    (h : convergenceReady s) :
    compactnessReady s := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

def identitySubsequence : SubsequenceSchema :=
  { indexMap := fun n => n, tightFamily := 0 ≤ 1, limitIdentified := 1 ≤ 1 }

example : strictlyIncreasing (fun n : ℕ => n) := by
  intro n
  exact Nat.lt_succ_self n

example : convergenceReady identitySubsequence := by
  unfold convergenceReady compactnessReady strictlyIncreasing identitySubsequence
  constructor
  · constructor
    · intro n
      exact Nat.lt_succ_self n
    · norm_num
  · norm_num

structure SubsequenceWindow where
  initialIndex : ℕ
  terminalIndex : ℕ
  tightnessBudget : ℕ
  extractionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubsequenceWindow.indicesControlled (w : SubsequenceWindow) : Prop :=
  w.initialIndex ≤ w.terminalIndex + w.slack

def subsequenceWindowReady (w : SubsequenceWindow) : Prop :=
  w.indicesControlled ∧
    w.extractionBudget ≤ w.terminalIndex + w.tightnessBudget + w.slack

def SubsequenceWindow.certificate (w : SubsequenceWindow) : ℕ :=
  w.initialIndex + w.terminalIndex + w.tightnessBudget + w.extractionBudget + w.slack

theorem subsequence_extractionBudget_le_certificate (w : SubsequenceWindow) :
    w.extractionBudget ≤ w.certificate := by
  unfold SubsequenceWindow.certificate
  omega

def sampleSubsequenceWindow : SubsequenceWindow :=
  { initialIndex := 2, terminalIndex := 6, tightnessBudget := 4,
    extractionBudget := 11, slack := 1 }

example : subsequenceWindowReady sampleSubsequenceWindow := by
  norm_num [subsequenceWindowReady, SubsequenceWindow.indicesControlled,
    sampleSubsequenceWindow]


structure SubsequenceLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubsequenceLimitSchemasBudgetCertificate.controlled
    (c : SubsequenceLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SubsequenceLimitSchemasBudgetCertificate.budgetControlled
    (c : SubsequenceLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SubsequenceLimitSchemasBudgetCertificate.Ready
    (c : SubsequenceLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SubsequenceLimitSchemasBudgetCertificate.size
    (c : SubsequenceLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem subsequenceLimitSchemas_budgetCertificate_le_size
    (c : SubsequenceLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSubsequenceLimitSchemasBudgetCertificate :
    SubsequenceLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSubsequenceLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SubsequenceLimitSchemasBudgetCertificate.controlled,
      sampleSubsequenceLimitSchemasBudgetCertificate]
  · norm_num [SubsequenceLimitSchemasBudgetCertificate.budgetControlled,
      sampleSubsequenceLimitSchemasBudgetCertificate]

example : sampleSubsequenceLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SubsequenceLimitSchemasBudgetCertificate.controlled,
      sampleSubsequenceLimitSchemasBudgetCertificate]
  · norm_num [SubsequenceLimitSchemasBudgetCertificate.budgetControlled,
      sampleSubsequenceLimitSchemasBudgetCertificate]

example :
    sampleSubsequenceLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSubsequenceLimitSchemasBudgetCertificate.size := by
  apply subsequenceLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [SubsequenceLimitSchemasBudgetCertificate.controlled,
      sampleSubsequenceLimitSchemasBudgetCertificate]
  · norm_num [SubsequenceLimitSchemasBudgetCertificate.budgetControlled,
      sampleSubsequenceLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleSubsequenceLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSubsequenceLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SubsequenceLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSubsequenceLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSubsequenceLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.SubsequenceLimitSchemas
