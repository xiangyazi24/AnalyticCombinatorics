import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Localization of singularities

Finite exclusion disks, contour windows, and singularity-localization
certificates.
-/

namespace AnalyticCombinatorics.PartB.Ch4.LocalizationOfSingularities

structure LocalizedSingularity where
  radiusWindow : ℕ
  multiplicityWindow : ℕ
  exclusionMargin : ℕ
deriving DecidableEq, Repr

def LocalizedSingularity.ready (s : LocalizedSingularity) : Prop :=
  0 < s.radiusWindow ∧ 0 < s.multiplicityWindow

def excludedByMargin (s : LocalizedSingularity) (disk : ℕ) : Bool :=
  disk + s.exclusionMargin < s.radiusWindow

theorem excludedByMargin_implies_lt
    {s : LocalizedSingularity} {disk : ℕ}
    (h : excludedByMargin s disk = true) :
    disk + s.exclusionMargin < s.radiusWindow := by
  unfold excludedByMargin at h
  exact of_decide_eq_true h

def annulusSeparated (inner outer margin : ℕ) : Prop :=
  inner + margin < outer

theorem annulusSeparated_sample :
    annulusSeparated 3 8 2 := by
  norm_num [annulusSeparated]

def localizedRadiusEnvelope (s : LocalizedSingularity) : ℕ :=
  s.radiusWindow + s.multiplicityWindow + s.exclusionMargin

theorem localizedRadius_le_envelope (s : LocalizedSingularity) :
    s.radiusWindow ≤ localizedRadiusEnvelope s := by
  unfold localizedRadiusEnvelope
  omega

def sampleLocalizedSingularity : LocalizedSingularity :=
  { radiusWindow := 7
    multiplicityWindow := 1
    exclusionMargin := 2 }

example : excludedByMargin sampleLocalizedSingularity 4 = true := by
  unfold excludedByMargin sampleLocalizedSingularity
  native_decide

example : localizedRadiusEnvelope sampleLocalizedSingularity = 10 := by
  unfold localizedRadiusEnvelope sampleLocalizedSingularity
  native_decide

theorem localizedSingularity_sample :
    sampleLocalizedSingularity.ready ∧
      excludedByMargin sampleLocalizedSingularity 4 = true := by
  norm_num [LocalizedSingularity.ready, excludedByMargin,
    sampleLocalizedSingularity]

def localizedSingularityListReady
    (disk : ℕ) (data : List LocalizedSingularity) : Bool :=
  data.all fun s =>
    0 < s.radiusWindow &&
      0 < s.multiplicityWindow &&
        excludedByMargin s disk

theorem localizedSingularityList_readyWindow :
    localizedSingularityListReady 4
      [sampleLocalizedSingularity,
       { radiusWindow := 9, multiplicityWindow := 2,
         exclusionMargin := 3 }] = true := by
  unfold localizedSingularityListReady excludedByMargin
    sampleLocalizedSingularity
  native_decide

structure LocalizationOfSingularitiesBudgetCertificate where
  diskWindow : ℕ
  contourWindow : ℕ
  exclusionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalizationOfSingularitiesBudgetCertificate.controlled
    (c : LocalizationOfSingularitiesBudgetCertificate) : Prop :=
  0 < c.diskWindow ∧
    c.exclusionWindow ≤ c.diskWindow + c.contourWindow + c.slack

def LocalizationOfSingularitiesBudgetCertificate.budgetControlled
    (c : LocalizationOfSingularitiesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.diskWindow + c.contourWindow + c.exclusionWindow + c.slack

def LocalizationOfSingularitiesBudgetCertificate.Ready
    (c : LocalizationOfSingularitiesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LocalizationOfSingularitiesBudgetCertificate.size
    (c : LocalizationOfSingularitiesBudgetCertificate) : ℕ :=
  c.diskWindow + c.contourWindow + c.exclusionWindow + c.slack

theorem localizationOfSingularities_budgetCertificate_le_size
    (c : LocalizationOfSingularitiesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleLocalizationOfSingularitiesBudgetCertificate :
    LocalizationOfSingularitiesBudgetCertificate :=
  { diskWindow := 4
    contourWindow := 5
    exclusionWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

example : sampleLocalizationOfSingularitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalizationOfSingularitiesBudgetCertificate.controlled,
      sampleLocalizationOfSingularitiesBudgetCertificate]
  · norm_num [LocalizationOfSingularitiesBudgetCertificate.budgetControlled,
      sampleLocalizationOfSingularitiesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLocalizationOfSingularitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalizationOfSingularitiesBudgetCertificate.controlled,
      sampleLocalizationOfSingularitiesBudgetCertificate]
  · norm_num [LocalizationOfSingularitiesBudgetCertificate.budgetControlled,
      sampleLocalizationOfSingularitiesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLocalizationOfSingularitiesBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalizationOfSingularitiesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LocalizationOfSingularitiesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLocalizationOfSingularitiesBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLocalizationOfSingularitiesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.LocalizationOfSingularities
