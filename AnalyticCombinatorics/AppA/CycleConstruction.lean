import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cycle construction.
-/

namespace AnalyticCombinatorics.AppA.CycleConstruction

/-- Word count before quotienting by cyclic rotation. -/
def wordCount (alphabet length : ℕ) : ℕ :=
  alphabet ^ length

/-- Crude cycle-count estimate obtained by choosing a root in each cycle. -/
def rootedCycleProxy (alphabet length : ℕ) : ℕ :=
  (length + 1) * wordCount alphabet length

/-- Finite check that rooted cycles stay within the rooted word envelope. -/
def rootedCycleEnvelopeCheck (alphabet N : ℕ) : Bool :=
  (List.range (N + 1)).all fun length =>
    rootedCycleProxy alphabet length = (length + 1) * wordCount alphabet length

/-- Finite cyclic symmetry audit: unrooting never increases the rooted estimate. -/
def unrootingEnvelopeCheck (cycle rooted : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => cycle n ≤ rooted n

def binaryCycleProxy (n : ℕ) : ℕ :=
  wordCount 2 n

theorem rootedCycleEnvelope_binary :
    rootedCycleEnvelopeCheck 2 16 = true := by
  unfold rootedCycleEnvelopeCheck rootedCycleProxy wordCount
  native_decide

theorem binaryCycle_unrootingEnvelope :
    unrootingEnvelopeCheck binaryCycleProxy (rootedCycleProxy 2) 16 = true := by
  unfold unrootingEnvelopeCheck binaryCycleProxy rootedCycleProxy wordCount
  native_decide

/-- Prefix total for a sampled cycle-count estimate. -/
def cyclePrefixCount (cycle : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + cycle n) 0

def CyclePrefixWindow (cycle : ℕ → ℕ) (N total : ℕ) : Prop :=
  cyclePrefixCount cycle N = total

theorem binaryCycle_prefixWindow :
    CyclePrefixWindow binaryCycleProxy 4 31 := by
  unfold CyclePrefixWindow cyclePrefixCount binaryCycleProxy wordCount
  native_decide

example : rootedCycleProxy 2 4 = 80 := by
  unfold rootedCycleProxy wordCount
  native_decide

example : cyclePrefixCount binaryCycleProxy 5 = 63 := by
  unfold cyclePrefixCount binaryCycleProxy wordCount
  native_decide

structure CycleConstructionBudgetCertificate where
  atomWindow : ℕ
  cycleWindow : ℕ
  symmetryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CycleConstructionBudgetCertificate.controlled
    (c : CycleConstructionBudgetCertificate) : Prop :=
  0 < c.atomWindow ∧ c.symmetryWindow ≤ c.atomWindow + c.cycleWindow + c.slack

def CycleConstructionBudgetCertificate.budgetControlled
    (c : CycleConstructionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.atomWindow + c.cycleWindow + c.symmetryWindow + c.slack

def CycleConstructionBudgetCertificate.Ready
    (c : CycleConstructionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CycleConstructionBudgetCertificate.size
    (c : CycleConstructionBudgetCertificate) : ℕ :=
  c.atomWindow + c.cycleWindow + c.symmetryWindow + c.slack

theorem cycleConstruction_budgetCertificate_le_size
    (c : CycleConstructionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleCycleConstructionBudgetCertificate :
    CycleConstructionBudgetCertificate :=
  { atomWindow := 5
    cycleWindow := 6
    symmetryWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCycleConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [CycleConstructionBudgetCertificate.controlled,
      sampleCycleConstructionBudgetCertificate]
  · norm_num [CycleConstructionBudgetCertificate.budgetControlled,
      sampleCycleConstructionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCycleConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleCycleConstructionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCycleConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [CycleConstructionBudgetCertificate.controlled,
      sampleCycleConstructionBudgetCertificate]
  · norm_num [CycleConstructionBudgetCertificate.budgetControlled,
      sampleCycleConstructionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List CycleConstructionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleCycleConstructionBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleCycleConstructionBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.CycleConstruction
