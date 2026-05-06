import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Surjection examples.

The number of surjections from an `n`-element set onto a `k`-element set is
`k! * S(n,k)`, with `S` the Stirling number of the second kind.
-/

namespace AnalyticCombinatorics.Examples.Surjections

def stirlingSecond : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k

def surjectionCount (n k : ℕ) : ℕ :=
  k.factorial * stirlingSecond n k

example : surjectionCount 0 0 = 1 := by native_decide
example : surjectionCount 1 1 = 1 := by native_decide
example : surjectionCount 2 1 = 1 := by native_decide
example : surjectionCount 2 2 = 2 := by native_decide
example : surjectionCount 3 2 = 6 := by native_decide
example : surjectionCount 3 3 = 6 := by native_decide
example : surjectionCount 4 2 = 14 := by native_decide
example : surjectionCount 4 3 = 36 := by native_decide
example : surjectionCount 5 3 = 150 := by native_decide

theorem surjectionCount_self_upto_8 :
    (List.range 9).all
      (fun n => surjectionCount n n == n.factorial) = true := by
  native_decide

structure SurjectionProfile where
  domainSize : ℕ
  codomainSize : ℕ
  occupiedFibers : ℕ
  collisionSlack : ℕ
deriving DecidableEq, Repr

def SurjectionProfile.ready (p : SurjectionProfile) : Prop :=
  p.occupiedFibers = p.codomainSize ∧
    p.codomainSize ≤ p.domainSize + p.collisionSlack

def SurjectionProfile.hasNonemptyCodomain (p : SurjectionProfile) : Prop :=
  0 < p.codomainSize

def SurjectionProfile.certificate (p : SurjectionProfile) : ℕ :=
  p.domainSize + p.codomainSize + p.occupiedFibers + p.collisionSlack

theorem codomainSize_le_certificate (p : SurjectionProfile) :
    p.codomainSize ≤ p.certificate := by
  unfold SurjectionProfile.certificate
  omega

theorem occupiedFibers_le_certificate (p : SurjectionProfile) :
    p.occupiedFibers ≤ p.certificate := by
  unfold SurjectionProfile.certificate
  omega

def sampleSurjectionProfile : SurjectionProfile :=
  { domainSize := 5, codomainSize := 3, occupiedFibers := 3, collisionSlack := 0 }

example : sampleSurjectionProfile.ready := by
  norm_num [sampleSurjectionProfile, SurjectionProfile.ready]

example : sampleSurjectionProfile.hasNonemptyCodomain := by
  norm_num [sampleSurjectionProfile, SurjectionProfile.hasNonemptyCodomain]

example : sampleSurjectionProfile.certificate = 11 := by
  norm_num [sampleSurjectionProfile, SurjectionProfile.certificate]

structure SurjectionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SurjectionsBudgetCertificate.controlled
    (c : SurjectionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SurjectionsBudgetCertificate.budgetControlled
    (c : SurjectionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SurjectionsBudgetCertificate.Ready (c : SurjectionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SurjectionsBudgetCertificate.size (c : SurjectionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem surjections_budgetCertificate_le_size
    (c : SurjectionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSurjectionsBudgetCertificate : SurjectionsBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleSurjectionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SurjectionsBudgetCertificate.controlled,
      sampleSurjectionsBudgetCertificate]
  · norm_num [SurjectionsBudgetCertificate.budgetControlled,
      sampleSurjectionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSurjectionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SurjectionsBudgetCertificate.controlled,
      sampleSurjectionsBudgetCertificate]
  · norm_num [SurjectionsBudgetCertificate.budgetControlled,
      sampleSurjectionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSurjectionsBudgetCertificate.certificateBudgetWindow ≤
      sampleSurjectionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SurjectionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSurjectionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSurjectionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.Surjections
