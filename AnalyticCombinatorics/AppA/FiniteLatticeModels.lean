import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite lattice models.

The module records elementary meet/join-style calculations on natural
budgets used by coefficient tables and finite posets.
-/

namespace AnalyticCombinatorics.AppA.FiniteLatticeModels

def finiteMeet (a b : ℕ) : ℕ :=
  min a b

def finiteJoin (a b : ℕ) : ℕ :=
  max a b

def boundedBetween (lo x hi : ℕ) : Prop :=
  lo ≤ x ∧ x ≤ hi

theorem finiteMeet_le_left (a b : ℕ) :
    finiteMeet a b ≤ a := by
  unfold finiteMeet
  exact min_le_left a b

theorem le_finiteJoin_left (a b : ℕ) :
    a ≤ finiteJoin a b := by
  unfold finiteJoin
  exact le_max_left a b

theorem boundedBetween_mono_right {lo x hi hi' : ℕ}
    (h : boundedBetween lo x hi) (hh : hi ≤ hi') :
    boundedBetween lo x hi' := by
  exact ⟨h.1, le_trans h.2 hh⟩

example : finiteMeet 7 3 = 3 := by
  native_decide

example : finiteJoin 7 3 = 7 := by
  native_decide

example : boundedBetween 2 5 9 := by
  norm_num [boundedBetween]

structure LatticeWindow where
  lower : ℕ
  middle : ℕ
  upper : ℕ
  joinBudget : ℕ
  meetSlack : ℕ
deriving DecidableEq, Repr

def LatticeWindow.bounded (w : LatticeWindow) : Prop :=
  boundedBetween w.lower w.middle w.upper

def LatticeWindow.joinControlled (w : LatticeWindow) : Prop :=
  finiteJoin w.middle w.upper ≤ w.joinBudget + w.meetSlack

def LatticeWindow.ready (w : LatticeWindow) : Prop :=
  w.bounded ∧ w.joinControlled

def LatticeWindow.certificate (w : LatticeWindow) : ℕ :=
  w.lower + w.middle + w.upper + w.joinBudget + w.meetSlack

theorem middle_le_certificate (w : LatticeWindow) :
    w.middle ≤ w.certificate := by
  unfold LatticeWindow.certificate
  omega

def sampleLatticeWindow : LatticeWindow :=
  { lower := 2, middle := 5, upper := 9, joinBudget := 9, meetSlack := 0 }

example : sampleLatticeWindow.ready := by
  norm_num [sampleLatticeWindow, LatticeWindow.ready, LatticeWindow.bounded,
    LatticeWindow.joinControlled, boundedBetween, finiteJoin]


structure FiniteLatticeModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteLatticeModelsBudgetCertificate.controlled
    (c : FiniteLatticeModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteLatticeModelsBudgetCertificate.budgetControlled
    (c : FiniteLatticeModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteLatticeModelsBudgetCertificate.Ready
    (c : FiniteLatticeModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteLatticeModelsBudgetCertificate.size
    (c : FiniteLatticeModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteLatticeModels_budgetCertificate_le_size
    (c : FiniteLatticeModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteLatticeModelsBudgetCertificate :
    FiniteLatticeModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteLatticeModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLatticeModelsBudgetCertificate.controlled,
      sampleFiniteLatticeModelsBudgetCertificate]
  · norm_num [FiniteLatticeModelsBudgetCertificate.budgetControlled,
      sampleFiniteLatticeModelsBudgetCertificate]

example :
    sampleFiniteLatticeModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLatticeModelsBudgetCertificate.size := by
  apply finiteLatticeModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteLatticeModelsBudgetCertificate.controlled,
      sampleFiniteLatticeModelsBudgetCertificate]
  · norm_num [FiniteLatticeModelsBudgetCertificate.budgetControlled,
      sampleFiniteLatticeModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteLatticeModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLatticeModelsBudgetCertificate.controlled,
      sampleFiniteLatticeModelsBudgetCertificate]
  · norm_num [FiniteLatticeModelsBudgetCertificate.budgetControlled,
      sampleFiniteLatticeModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteLatticeModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLatticeModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteLatticeModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteLatticeModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteLatticeModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteLatticeModels
