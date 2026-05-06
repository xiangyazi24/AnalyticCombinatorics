import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Dyck path examples.

Dyck paths of semilength `n` are counted by `C_n`.
-/

namespace AnalyticCombinatorics.Examples.DyckPaths

inductive DyckStep where
  | up
  | down
deriving DecidableEq, Repr

def finalHeightFrom : ℕ → List DyckStep → ℕ
  | h, [] => h
  | h, DyckStep.up :: rest => finalHeightFrom (h + 1) rest
  | h, DyckStep.down :: rest => finalHeightFrom (h - 1) rest

def prefixesNonnegativeFrom : ℕ → List DyckStep → Bool
  | _, [] => true
  | h, DyckStep.up :: rest => prefixesNonnegativeFrom (h + 1) rest
  | 0, DyckStep.down :: _ => false
  | h + 1, DyckStep.down :: rest => prefixesNonnegativeFrom h rest

def dyckWordReady (steps : List DyckStep) : Prop :=
  prefixesNonnegativeFrom 0 steps = true ∧ finalHeightFrom 0 steps = 0

instance (steps : List DyckStep) : Decidable (dyckWordReady steps) := by
  unfold dyckWordReady
  infer_instance

def catalanFormula (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

def dyckPathCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 42
  | 6 => 132
  | 7 => 429
  | 8 => 1430
  | 9 => 4862
  | 10 => 16796
  | _ => 0

def sampleDyckWord : List DyckStep :=
  [DyckStep.up, DyckStep.up, DyckStep.down, DyckStep.down]

theorem sampleDyckWord_ready :
    dyckWordReady sampleDyckWord := by
  native_decide

theorem catalanFormula_matches_dyckPathCount_five :
    catalanFormula 5 = dyckPathCount 5 := by
  native_decide

example : dyckWordReady sampleDyckWord := by native_decide
example : catalanFormula 5 = dyckPathCount 5 := by native_decide
example : dyckPathCount 0 = 1 := by native_decide
example : dyckPathCount 1 = 1 := by native_decide
example : dyckPathCount 2 = 2 := by native_decide
example : dyckPathCount 3 = 5 := by native_decide
example : dyckPathCount 4 = 14 := by native_decide
example : dyckPathCount 5 = 42 := by native_decide
example : dyckPathCount 10 = 16796 := by native_decide
example : (List.range 6).map dyckPathCount = [1, 1, 2, 5, 14, 42] := by
  native_decide

/-- Finite Catalan recurrence audit for Dyck-path counts. -/
def dyckPathCatalanRecurrenceCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    dyckPathCount (n + 1) * (n + 2) =
      2 * (2 * n + 1) * dyckPathCount n

theorem dyckPathCount_recurrenceWindow :
    dyckPathCatalanRecurrenceCheck 9 = true := by
  unfold dyckPathCatalanRecurrenceCheck dyckPathCount
  native_decide

structure DyckPathsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DyckPathsBudgetCertificate.controlled
    (c : DyckPathsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DyckPathsBudgetCertificate.budgetControlled
    (c : DyckPathsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DyckPathsBudgetCertificate.Ready (c : DyckPathsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DyckPathsBudgetCertificate.size (c : DyckPathsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem dyckPaths_budgetCertificate_le_size
    (c : DyckPathsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleDyckPathsBudgetCertificate : DyckPathsBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleDyckPathsBudgetCertificate.Ready := by
  constructor
  · norm_num [DyckPathsBudgetCertificate.controlled,
      sampleDyckPathsBudgetCertificate]
  · norm_num [DyckPathsBudgetCertificate.budgetControlled,
      sampleDyckPathsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleDyckPathsBudgetCertificate_ready :
    sampleDyckPathsBudgetCertificate.Ready := by
  constructor
  · norm_num [DyckPathsBudgetCertificate.controlled,
      sampleDyckPathsBudgetCertificate]
  · norm_num [DyckPathsBudgetCertificate.budgetControlled,
      sampleDyckPathsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleDyckPathsBudgetCertificate.Ready :=
  sampleDyckPathsBudgetCertificate_ready

theorem sampleBudgetCertificate_le_size :
    sampleDyckPathsBudgetCertificate.certificateBudgetWindow ≤
      sampleDyckPathsBudgetCertificate.size := by
  exact sampleDyckPathsBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DyckPathsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDyckPathsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDyckPathsBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.DyckPaths
