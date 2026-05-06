import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bender method windows.
-/

namespace AnalyticCombinatorics.Asymptotics.BenderMethod

/-- Fibonacci model for second-order recurrence windows. -/
def fibModel : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibModel (n + 1) + fibModel n

/-- Finite audit for a homogeneous second-order recurrence. -/
def secondOrderRecurrenceCheck
    (a : ℕ → ℕ) (c0 c1 N : ℕ) : Bool :=
  (List.range N).all fun n => a (n + 2) = c1 * a (n + 1) + c0 * a n

/-- Finite coefficient-envelope audit for Bender-style recurrences. -/
def coefficientEnvelopeCheck
    (a envelope : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => a n ≤ envelope n

def BenderRecurrenceWindow
    (a envelope : ℕ → ℕ) (c0 c1 N : ℕ) : Prop :=
  secondOrderRecurrenceCheck a c0 c1 N = true ∧
    coefficientEnvelopeCheck a envelope N = true

theorem fibModel_benderRecurrenceWindow :
    BenderRecurrenceWindow fibModel (fun n => 2 ^ n) 1 1 20 := by
  unfold BenderRecurrenceWindow secondOrderRecurrenceCheck
    coefficientEnvelopeCheck fibModel
  native_decide

theorem geometric_benderRecurrenceWindow :
    BenderRecurrenceWindow (fun n => 3 ^ n) (fun n => 3 ^ n) 0 3 12 := by
  unfold BenderRecurrenceWindow secondOrderRecurrenceCheck
    coefficientEnvelopeCheck
  native_decide

/-- Prefix sum of a recurrence model for finite Bender windows. -/
def recurrencePrefixSum (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + a n) 0

theorem fibModel_prefixWindow :
    recurrencePrefixSum fibModel 7 = 33 := by
  unfold recurrencePrefixSum fibModel
  native_decide

example : fibModel 8 = 21 := by
  unfold fibModel
  native_decide

example : recurrencePrefixSum (fun n => 3 ^ n) 3 = 40 := by
  unfold recurrencePrefixSum
  native_decide

structure BenderMethodBudgetCertificate where
  recurrenceWindow : ℕ
  coefficientWindow : ℕ
  errorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BenderMethodBudgetCertificate.controlled
    (c : BenderMethodBudgetCertificate) : Prop :=
  0 < c.recurrenceWindow ∧
    c.errorWindow ≤ c.recurrenceWindow + c.coefficientWindow + c.slack

def BenderMethodBudgetCertificate.budgetControlled
    (c : BenderMethodBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.recurrenceWindow + c.coefficientWindow + c.errorWindow + c.slack

def BenderMethodBudgetCertificate.Ready
    (c : BenderMethodBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BenderMethodBudgetCertificate.size
    (c : BenderMethodBudgetCertificate) : ℕ :=
  c.recurrenceWindow + c.coefficientWindow + c.errorWindow + c.slack

theorem benderMethod_budgetCertificate_le_size
    (c : BenderMethodBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBenderMethodBudgetCertificate :
    BenderMethodBudgetCertificate :=
  { recurrenceWindow := 5
    coefficientWindow := 6
    errorWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBenderMethodBudgetCertificate_ready :
    sampleBenderMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [BenderMethodBudgetCertificate.controlled,
      sampleBenderMethodBudgetCertificate]
  · norm_num [BenderMethodBudgetCertificate.budgetControlled,
      sampleBenderMethodBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleBenderMethodBudgetCertificate.Ready :=
  sampleBenderMethodBudgetCertificate_ready

example : sampleBenderMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [BenderMethodBudgetCertificate.controlled,
      sampleBenderMethodBudgetCertificate]
  · norm_num [BenderMethodBudgetCertificate.budgetControlled,
      sampleBenderMethodBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleBenderMethodBudgetCertificate.certificateBudgetWindow ≤
      sampleBenderMethodBudgetCertificate.size := by
  exact sampleBenderMethodBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List BenderMethodBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBenderMethodBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBenderMethodBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.BenderMethod
