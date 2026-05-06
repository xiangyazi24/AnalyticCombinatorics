import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Sets and the exp-log schema.

Finite bookkeeping for labelled set constructions with logarithmic
singular profiles.
-/

namespace AnalyticCombinatorics.PartB.Ch7.SetsExpLogSchema

/-- Finite set construction coefficient: subsets of an `n`-set. -/
def setConstructionCoeff (n : ℕ) : ℕ :=
  2 ^ n

/-- Logarithmic scale for exp-log schemas. -/
def logSchemaProxy (n : ℕ) : ℕ :=
  Nat.log2 (n + 2) + 1

/-- Finite exp-log envelope check. -/
def expLogEnvelopeCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    logSchemaProxy n ≤ setConstructionCoeff n + 1

theorem expLogEnvelope_window :
    expLogEnvelopeCheck 32 = true := by
  unfold expLogEnvelopeCheck logSchemaProxy setConstructionCoeff
  native_decide

/-- Finite monotonicity audit for the logarithmic scale. -/
def logSchemaMonotoneCheck (N : ℕ) : Bool :=
  (List.range N).all fun n => logSchemaProxy n ≤ logSchemaProxy (n + 1)

theorem logSchema_monotoneWindow :
    logSchemaMonotoneCheck 32 = true := by
  unfold logSchemaMonotoneCheck logSchemaProxy
  native_decide

structure ExpLogSchemaWindow where
  setComponentWindow : ℕ
  exponentialWindow : ℕ
  logarithmicWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def expLogSchemaReady (w : ExpLogSchemaWindow) : Prop :=
  0 < w.setComponentWindow ∧
    w.logarithmicWindow ≤
      w.setComponentWindow + w.exponentialWindow + w.slack

def expLogSchemaBudget (w : ExpLogSchemaWindow) : ℕ :=
  w.setComponentWindow + w.exponentialWindow +
    w.logarithmicWindow + w.slack

theorem logarithmicWindow_le_expLogSchemaBudget
    (w : ExpLogSchemaWindow) :
    w.logarithmicWindow ≤ expLogSchemaBudget w := by
  unfold expLogSchemaBudget
  omega

def sampleExpLogSchemaWindow : ExpLogSchemaWindow :=
  { setComponentWindow := 5
    exponentialWindow := 4
    logarithmicWindow := 8
    slack := 1 }

example : expLogSchemaReady sampleExpLogSchemaWindow := by
  norm_num [expLogSchemaReady, sampleExpLogSchemaWindow]

structure SetsExpLogSchemaBudgetCertificate where
  setWindow : ℕ
  expWindow : ℕ
  logWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SetsExpLogSchemaBudgetCertificate.controlled
    (c : SetsExpLogSchemaBudgetCertificate) : Prop :=
  0 < c.setWindow ∧ c.logWindow ≤ c.setWindow + c.expWindow + c.slack

def SetsExpLogSchemaBudgetCertificate.budgetControlled
    (c : SetsExpLogSchemaBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.setWindow + c.expWindow + c.logWindow + c.slack

def SetsExpLogSchemaBudgetCertificate.Ready
    (c : SetsExpLogSchemaBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SetsExpLogSchemaBudgetCertificate.size
    (c : SetsExpLogSchemaBudgetCertificate) : ℕ :=
  c.setWindow + c.expWindow + c.logWindow + c.slack

theorem setsExpLogSchema_budgetCertificate_le_size
    (c : SetsExpLogSchemaBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSetsExpLogSchemaBudgetCertificate :
    SetsExpLogSchemaBudgetCertificate :=
  { setWindow := 5
    expWindow := 4
    logWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSetsExpLogSchemaBudgetCertificate.Ready := by
  constructor
  · norm_num [SetsExpLogSchemaBudgetCertificate.controlled,
      sampleSetsExpLogSchemaBudgetCertificate]
  · norm_num [SetsExpLogSchemaBudgetCertificate.budgetControlled,
      sampleSetsExpLogSchemaBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSetsExpLogSchemaBudgetCertificate.certificateBudgetWindow ≤
      sampleSetsExpLogSchemaBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSetsExpLogSchemaBudgetCertificate.Ready := by
  constructor
  · norm_num [SetsExpLogSchemaBudgetCertificate.controlled,
      sampleSetsExpLogSchemaBudgetCertificate]
  · norm_num [SetsExpLogSchemaBudgetCertificate.budgetControlled,
      sampleSetsExpLogSchemaBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SetsExpLogSchemaBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSetsExpLogSchemaBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSetsExpLogSchemaBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.SetsExpLogSchema
