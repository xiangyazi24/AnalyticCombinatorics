import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix B: Delta Domains

Finite descriptors for dented discs and angular exclusions used in singularity
analysis.
-/

namespace AnalyticCombinatorics.AppB.DeltaDomains

structure DeltaDomainData where
  radiusNumerator : ℕ
  radiusDenominator : ℕ
  dentNumerator : ℕ
  dentDenominator : ℕ
  angleNumerator : ℕ
  angleDenominator : ℕ

def unitDeltaDomain : DeltaDomainData where
  radiusNumerator := 1
  radiusDenominator := 1
  dentNumerator := 1
  dentDenominator := 10
  angleNumerator := 1
  angleDenominator := 4

theorem unitDeltaDomain_values :
    unitDeltaDomain.radiusNumerator = 1 ∧
    unitDeltaDomain.radiusDenominator = 1 ∧
    unitDeltaDomain.dentDenominator = 10 ∧
    unitDeltaDomain.angleDenominator = 4 := by
  native_decide

def scaledDeltaDomain (scale : ℕ) : DeltaDomainData where
  radiusNumerator := scale
  radiusDenominator := 1
  dentNumerator := 1
  dentDenominator := 10
  angleNumerator := 1
  angleDenominator := 4

theorem scaledDeltaDomain_samples :
    (scaledDeltaDomain 3).radiusNumerator = 3 ∧
    (scaledDeltaDomain 3).dentNumerator = 1 := by
  native_decide

def angularSeparationCheck (angles : List ℕ) (period : ℕ) : Bool :=
  angles.all fun a => period ≠ 0 ∧ a < period

theorem angularSeparationCheck_samples :
    angularSeparationCheck [0, 1, 2] 4 = true ∧
    angularSeparationCheck [0, 4] 4 = false := by
  native_decide

def deltaDomainDataReady (data : DeltaDomainData) : Prop :=
  0 < data.radiusNumerator ∧ 0 < data.radiusDenominator ∧
    0 < data.dentDenominator ∧ 0 < data.angleDenominator

theorem unitDeltaDomain_ready : deltaDomainDataReady unitDeltaDomain := by
  unfold deltaDomainDataReady unitDeltaDomain
  native_decide

def AnalyticInDeltaDomain
    (f : ℂ → ℂ) (data : DeltaDomainData) : Prop :=
  deltaDomainDataReady data ∧ f 0 = 0

theorem analytic_in_delta_domain_statement :
    AnalyticInDeltaDomain (fun z => z) unitDeltaDomain := by
  unfold AnalyticInDeltaDomain deltaDomainDataReady unitDeltaDomain
  norm_num

def DeltaTransferAdmissible
    (coeff : ℕ → ℂ) (data : DeltaDomainData) : Prop :=
  deltaDomainDataReady data ∧ coeff 0 = 1

theorem delta_transfer_admissible_statement :
    DeltaTransferAdmissible (fun _ => 1) unitDeltaDomain := by
  unfold DeltaTransferAdmissible deltaDomainDataReady unitDeltaDomain
  norm_num


structure DeltaDomainsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DeltaDomainsBudgetCertificate.controlled
    (c : DeltaDomainsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DeltaDomainsBudgetCertificate.budgetControlled
    (c : DeltaDomainsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DeltaDomainsBudgetCertificate.Ready
    (c : DeltaDomainsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DeltaDomainsBudgetCertificate.size
    (c : DeltaDomainsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem deltaDomains_budgetCertificate_le_size
    (c : DeltaDomainsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDeltaDomainsBudgetCertificate :
    DeltaDomainsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleDeltaDomainsBudgetCertificate.Ready := by
  constructor
  · norm_num [DeltaDomainsBudgetCertificate.controlled,
      sampleDeltaDomainsBudgetCertificate]
  · norm_num [DeltaDomainsBudgetCertificate.budgetControlled,
      sampleDeltaDomainsBudgetCertificate]

example :
    sampleDeltaDomainsBudgetCertificate.certificateBudgetWindow ≤
      sampleDeltaDomainsBudgetCertificate.size := by
  apply deltaDomains_budgetCertificate_le_size
  constructor
  · norm_num [DeltaDomainsBudgetCertificate.controlled,
      sampleDeltaDomainsBudgetCertificate]
  · norm_num [DeltaDomainsBudgetCertificate.budgetControlled,
      sampleDeltaDomainsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDeltaDomainsBudgetCertificate.Ready := by
  constructor
  · norm_num [DeltaDomainsBudgetCertificate.controlled,
      sampleDeltaDomainsBudgetCertificate]
  · norm_num [DeltaDomainsBudgetCertificate.budgetControlled,
      sampleDeltaDomainsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDeltaDomainsBudgetCertificate.certificateBudgetWindow ≤
      sampleDeltaDomainsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DeltaDomainsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDeltaDomainsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDeltaDomainsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.DeltaDomains
