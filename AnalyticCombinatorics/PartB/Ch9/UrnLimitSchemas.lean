import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Urn limit-law schema bookkeeping.

The data records balance, replacement mass, and variance budget for
Pólya-like urn limit results.
-/

namespace AnalyticCombinatorics.PartB.Ch9.UrnLimitSchemas

structure UrnSchemaData where
  initialBalls : ℕ
  replacementMass : ℕ
  varianceBudget : ℕ
deriving DecidableEq, Repr

def nonemptyUrn (d : UrnSchemaData) : Prop :=
  0 < d.initialBalls

def balancedReplacement (d : UrnSchemaData) : Prop :=
  0 < d.replacementMass

def urnLimitReady (d : UrnSchemaData) : Prop :=
  nonemptyUrn d ∧ balancedReplacement d ∧ 0 < d.varianceBudget

def totalMassAfter (d : UrnSchemaData) (draws : ℕ) : ℕ :=
  d.initialBalls + draws * d.replacementMass

theorem urnLimitReady.nonempty {d : UrnSchemaData}
    (h : urnLimitReady d) :
    nonemptyUrn d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem totalMassAfter_succ (d : UrnSchemaData) (draws : ℕ) :
    totalMassAfter d (draws + 1) = totalMassAfter d draws + d.replacementMass := by
  unfold totalMassAfter
  rw [Nat.succ_mul]
  omega

def sampleUrn : UrnSchemaData :=
  { initialBalls := 5, replacementMass := 2, varianceBudget := 3 }

example : urnLimitReady sampleUrn := by
  norm_num [urnLimitReady, nonemptyUrn, balancedReplacement, sampleUrn]

example : totalMassAfter sampleUrn 4 = 13 := by
  native_decide

/-- Finite executable readiness audit for urn limit data. -/
def urnSchemaDataListReady (data : List UrnSchemaData) : Bool :=
  data.all fun d =>
    0 < d.initialBalls && 0 < d.replacementMass && 0 < d.varianceBudget

theorem urnSchemaDataList_readyWindow :
    urnSchemaDataListReady
      [{ initialBalls := 3, replacementMass := 1, varianceBudget := 2 },
       { initialBalls := 5, replacementMass := 2, varianceBudget := 3 }] = true := by
  unfold urnSchemaDataListReady
  native_decide

structure UrnLimitWindow where
  initialBalls : ℕ
  replacementMass : ℕ
  varianceBudget : ℕ
  drawBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UrnLimitWindow.drawControlled (w : UrnLimitWindow) : Prop :=
  w.drawBudget ≤ w.initialBalls + w.replacementMass + w.varianceBudget + w.slack

def urnLimitWindowReady (w : UrnLimitWindow) : Prop :=
  0 < w.initialBalls ∧
    0 < w.replacementMass ∧
    0 < w.varianceBudget ∧
    w.drawControlled

def UrnLimitWindow.certificate (w : UrnLimitWindow) : ℕ :=
  w.initialBalls + w.replacementMass + w.varianceBudget + w.slack

theorem urn_drawBudget_le_certificate {w : UrnLimitWindow}
    (h : urnLimitWindowReady w) :
    w.drawBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hdraw⟩
  exact hdraw

def sampleUrnLimitWindow : UrnLimitWindow :=
  { initialBalls := 5, replacementMass := 2, varianceBudget := 3, drawBudget := 9, slack := 0 }

example : urnLimitWindowReady sampleUrnLimitWindow := by
  norm_num [urnLimitWindowReady, UrnLimitWindow.drawControlled, sampleUrnLimitWindow]

example : sampleUrnLimitWindow.certificate = 10 := by
  native_decide


structure UrnLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UrnLimitSchemasBudgetCertificate.controlled
    (c : UrnLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UrnLimitSchemasBudgetCertificate.budgetControlled
    (c : UrnLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UrnLimitSchemasBudgetCertificate.Ready
    (c : UrnLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UrnLimitSchemasBudgetCertificate.size
    (c : UrnLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem urnLimitSchemas_budgetCertificate_le_size
    (c : UrnLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUrnLimitSchemasBudgetCertificate :
    UrnLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleUrnLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UrnLimitSchemasBudgetCertificate.controlled,
      sampleUrnLimitSchemasBudgetCertificate]
  · norm_num [UrnLimitSchemasBudgetCertificate.budgetControlled,
      sampleUrnLimitSchemasBudgetCertificate]

example :
    sampleUrnLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUrnLimitSchemasBudgetCertificate.size := by
  apply urnLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [UrnLimitSchemasBudgetCertificate.controlled,
      sampleUrnLimitSchemasBudgetCertificate]
  · norm_num [UrnLimitSchemasBudgetCertificate.budgetControlled,
      sampleUrnLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUrnLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UrnLimitSchemasBudgetCertificate.controlled,
      sampleUrnLimitSchemasBudgetCertificate]
  · norm_num [UrnLimitSchemasBudgetCertificate.budgetControlled,
      sampleUrnLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUrnLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUrnLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UrnLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUrnLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUrnLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.UrnLimitSchemas
