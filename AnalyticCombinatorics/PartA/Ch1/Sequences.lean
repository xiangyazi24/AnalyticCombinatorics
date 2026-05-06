import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Sequence construction schemas.

The finite model below uses lists over `Fin atoms` to represent SEQ(A).
-/

namespace AnalyticCombinatorics.PartA.Ch1.Sequences

def sequenceWords (atoms : ℕ) : ℕ → Finset (List (Fin atoms))
  | 0 => {[]}
  | n + 1 =>
      (Finset.univ.product (sequenceWords atoms n)).image
        (fun pair => pair.1 :: pair.2)

theorem mem_sequenceWords_length {atoms : ℕ} {xs : List (Fin atoms)} {n : ℕ} :
    xs ∈ sequenceWords atoms n ↔ xs.length = n := by
  revert xs
  induction n with
  | zero =>
      intro xs
      cases xs <;> simp [sequenceWords]
  | succ n ih =>
      intro xs
      cases xs with
      | nil =>
          simp [sequenceWords]
      | cons a xs =>
          simp [sequenceWords, ih]

def sequenceCount (atoms length : ℕ) : ℕ :=
  atoms ^ length

def sequenceCountByEnumeration (atoms length : ℕ) : ℕ :=
  (sequenceWords atoms length).card

def nonemptySequenceCount (atoms length : ℕ) : ℕ :=
  if length = 0 then 0 else sequenceCount atoms length

def sequenceBudget (atoms length slack : ℕ) : ℕ :=
  atoms + length + slack

def sequenceReady (atoms length slack : ℕ) : Prop :=
  0 < atoms ∧ length ≤ atoms + slack

structure SequenceWindow where
  atoms : ℕ
  length : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def sequenceWindowReady (w : SequenceWindow) : Prop :=
  sequenceReady w.atoms w.length w.slack

def sequenceWindowBudget (w : SequenceWindow) : ℕ :=
  sequenceBudget w.atoms w.length w.slack

theorem length_le_budget (atoms length slack : ℕ) :
    length ≤ sequenceBudget atoms length slack := by
  unfold sequenceBudget
  omega

theorem sequenceWindowReady.certificate {w : SequenceWindow}
    (h : sequenceWindowReady w) :
    0 < w.atoms ∧ w.length ≤ w.atoms + w.slack ∧
      w.length ≤ sequenceWindowBudget w := by
  rcases h with ⟨hatoms, hlength⟩
  refine ⟨hatoms, hlength, ?_⟩
  unfold sequenceWindowBudget sequenceBudget
  omega

def sampleSequenceWindow : SequenceWindow :=
  { atoms := 5, length := 7, slack := 2 }

example : sequenceReady 5 7 2 := by norm_num [sequenceReady]
example : sequenceBudget 5 7 2 = 14 := by native_decide
example : sequenceWindowReady sampleSequenceWindow := by
  norm_num [sequenceWindowReady, sequenceReady, sampleSequenceWindow]
example : sequenceWindowBudget sampleSequenceWindow = 14 := by native_decide
example : sequenceCount 2 5 = 32 := by native_decide
example : sequenceCountByEnumeration 2 4 = 16 := by native_decide
example : sequenceCountByEnumeration 3 3 = sequenceCount 3 3 := by native_decide
example : nonemptySequenceCount 3 0 = 0 := by native_decide
example : nonemptySequenceCount 3 2 = 9 := by native_decide


structure SequencesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SequencesBudgetCertificate.controlled
    (c : SequencesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SequencesBudgetCertificate.budgetControlled
    (c : SequencesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SequencesBudgetCertificate.Ready
    (c : SequencesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SequencesBudgetCertificate.size
    (c : SequencesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem sequences_budgetCertificate_le_size
    (c : SequencesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSequencesBudgetCertificate :
    SequencesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSequencesBudgetCertificate.Ready := by
  constructor
  · norm_num [SequencesBudgetCertificate.controlled,
      sampleSequencesBudgetCertificate]
  · norm_num [SequencesBudgetCertificate.budgetControlled,
      sampleSequencesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSequencesBudgetCertificate.certificateBudgetWindow ≤
      sampleSequencesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSequencesBudgetCertificate.Ready := by
  constructor
  · norm_num [SequencesBudgetCertificate.controlled,
      sampleSequencesBudgetCertificate]
  · norm_num [SequencesBudgetCertificate.budgetControlled,
      sampleSequencesBudgetCertificate]

example :
    sampleSequencesBudgetCertificate.certificateBudgetWindow ≤
      sampleSequencesBudgetCertificate.size := by
  apply sequences_budgetCertificate_le_size
  constructor
  · norm_num [SequencesBudgetCertificate.controlled,
      sampleSequencesBudgetCertificate]
  · norm_num [SequencesBudgetCertificate.budgetControlled,
      sampleSequencesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SequencesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSequencesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSequencesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.Sequences
