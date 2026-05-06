import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Localization of singularities.
-/

namespace AnalyticCombinatorics.PartB.Ch4.LocalizationSingularities

/-- Finite singularity candidate, represented by integer radius data. -/
structure SingularityCandidate where
  radius : ℕ
  multiplicity : ℕ
deriving DecidableEq, Repr

def SingularityCandidate.valid (s : SingularityCandidate) : Prop :=
  0 < s.radius ∧ 0 < s.multiplicity

/-- Finite check that every sampled singularity lies outside a disk. -/
def outsideDiskCheck
    (candidates : ℕ → SingularityCandidate) (diskRadius N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => diskRadius < (candidates n).radius

/-- Finite localization statement: a disk excludes sampled singularities. -/
def LocalizationWindow
    (candidates : ℕ → SingularityCandidate) (diskRadius N : ℕ) : Prop :=
  outsideDiskCheck candidates diskRadius N = true

def arithmeticSingularityCandidates (n : ℕ) : SingularityCandidate :=
  { radius := n + 2, multiplicity := 1 }

theorem arithmeticSingularityCandidates_valid :
    ∀ n : Fin 10, (arithmeticSingularityCandidates n.val).valid := by
  unfold arithmeticSingularityCandidates SingularityCandidate.valid
  native_decide

theorem localizationWindow_unitDisk :
    LocalizationWindow arithmeticSingularityCandidates 1 12 := by
  unfold LocalizationWindow outsideDiskCheck arithmeticSingularityCandidates
  native_decide

/-- Finite audit that sampled multiplicities are positive. -/
def multiplicityPositiveCheck
    (candidates : ℕ → SingularityCandidate) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => 0 < (candidates n).multiplicity

theorem arithmeticSingularityCandidates_multiplicityWindow :
    multiplicityPositiveCheck arithmeticSingularityCandidates 16 = true := by
  unfold multiplicityPositiveCheck arithmeticSingularityCandidates
  native_decide

example : (arithmeticSingularityCandidates 3).radius = 5 := by
  unfold arithmeticSingularityCandidates
  native_decide

example : outsideDiskCheck arithmeticSingularityCandidates 1 5 = true := by
  unfold outsideDiskCheck arithmeticSingularityCandidates
  native_decide

structure LocalizationSingularitiesBudgetCertificate where
  diskWindow : ℕ
  contourWindow : ℕ
  singularityWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalizationSingularitiesBudgetCertificate.controlled
    (c : LocalizationSingularitiesBudgetCertificate) : Prop :=
  0 < c.diskWindow ∧
    c.singularityWindow ≤ c.diskWindow + c.contourWindow + c.slack

def LocalizationSingularitiesBudgetCertificate.budgetControlled
    (c : LocalizationSingularitiesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.diskWindow + c.contourWindow + c.singularityWindow + c.slack

def LocalizationSingularitiesBudgetCertificate.Ready
    (c : LocalizationSingularitiesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LocalizationSingularitiesBudgetCertificate.size
    (c : LocalizationSingularitiesBudgetCertificate) : ℕ :=
  c.diskWindow + c.contourWindow + c.singularityWindow + c.slack

theorem localizationSingularities_budgetCertificate_le_size
    (c : LocalizationSingularitiesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleLocalizationSingularitiesBudgetCertificate :
    LocalizationSingularitiesBudgetCertificate :=
  { diskWindow := 5
    contourWindow := 6
    singularityWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLocalizationSingularitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalizationSingularitiesBudgetCertificate.controlled,
      sampleLocalizationSingularitiesBudgetCertificate]
  · norm_num [LocalizationSingularitiesBudgetCertificate.budgetControlled,
      sampleLocalizationSingularitiesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLocalizationSingularitiesBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalizationSingularitiesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLocalizationSingularitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalizationSingularitiesBudgetCertificate.controlled,
      sampleLocalizationSingularitiesBudgetCertificate]
  · norm_num [LocalizationSingularitiesBudgetCertificate.budgetControlled,
      sampleLocalizationSingularitiesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LocalizationSingularitiesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleLocalizationSingularitiesBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleLocalizationSingularitiesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.LocalizationSingularities
