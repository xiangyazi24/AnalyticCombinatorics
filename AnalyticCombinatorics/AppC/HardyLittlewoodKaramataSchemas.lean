import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Hardy-Littlewood-Karamata Tauberian schema bookkeeping.

The analytic hypotheses are represented by monotonicity, regular variation,
and a positive normalization budget.
-/

namespace AnalyticCombinatorics.AppC.HardyLittlewoodKaramataSchemas

structure HLKData where
  monotoneCoefficients : Prop
  regularVariation : Prop
  normalization : ℕ
deriving Repr

def positiveNormalization (d : HLKData) : Prop :=
  0 < d.normalization

def hlkReady (d : HLKData) : Prop :=
  d.monotoneCoefficients ∧ d.regularVariation ∧ positiveNormalization d

def normalizationScale (d : HLKData) : ℕ :=
  d.normalization + 1

theorem hlkReady.regular {d : HLKData}
    (h : hlkReady d) :
    d.regularVariation := h.2.1

theorem normalizationScale_positive (d : HLKData) :
    0 < normalizationScale d := by
  unfold normalizationScale
  omega

def sampleHLK : HLKData :=
  { monotoneCoefficients := 0 ≤ 6, regularVariation := 6 ≤ 6, normalization := 6 }

example : hlkReady sampleHLK := by
  norm_num [hlkReady, positiveNormalization, sampleHLK]

example : normalizationScale sampleHLK = 7 := by
  native_decide

structure KaramataWindow where
  cutoff : ℕ
  normalization : ℕ
  summatoryMass : ℕ
  regularVariationSlack : ℕ
deriving DecidableEq, Repr

def KaramataWindow.normalizationReady (w : KaramataWindow) : Prop :=
  0 < w.normalization

def KaramataWindow.summatoryControlled (w : KaramataWindow) : Prop :=
  w.summatoryMass ≤ w.cutoff * w.normalization + w.regularVariationSlack

def KaramataWindow.ready (w : KaramataWindow) : Prop :=
  w.normalizationReady ∧ w.summatoryControlled

def KaramataWindow.certificate (w : KaramataWindow) : ℕ :=
  w.cutoff + w.normalization + w.summatoryMass + w.regularVariationSlack

theorem summatoryMass_le_certificate (w : KaramataWindow) :
    w.summatoryMass ≤ w.certificate := by
  unfold KaramataWindow.certificate
  omega

def sampleKaramataWindow : KaramataWindow :=
  { cutoff := 4, normalization := 6, summatoryMass := 20, regularVariationSlack := 4 }

example : sampleKaramataWindow.ready := by
  norm_num [sampleKaramataWindow, KaramataWindow.ready,
    KaramataWindow.normalizationReady, KaramataWindow.summatoryControlled]

structure KaramataRefinementWindow where
  cutoffWindow : ℕ
  normalizationWindow : ℕ
  summatoryWindow : ℕ
  karamataBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KaramataRefinementWindow.summatoryControlled
    (w : KaramataRefinementWindow) : Prop :=
  w.summatoryWindow ≤ w.cutoffWindow * w.normalizationWindow + w.slack

def karamataRefinementWindowReady (w : KaramataRefinementWindow) : Prop :=
  0 < w.normalizationWindow ∧ w.summatoryControlled ∧
    w.karamataBudget ≤ w.cutoffWindow + w.summatoryWindow + w.slack

def KaramataRefinementWindow.certificate
    (w : KaramataRefinementWindow) : ℕ :=
  w.cutoffWindow + w.normalizationWindow + w.summatoryWindow + w.karamataBudget + w.slack

theorem karamataRefinement_budget_le_certificate
    (w : KaramataRefinementWindow) :
    w.karamataBudget ≤ w.certificate := by
  unfold KaramataRefinementWindow.certificate
  omega

def sampleKaramataRefinementWindow : KaramataRefinementWindow :=
  { cutoffWindow := 4, normalizationWindow := 6, summatoryWindow := 20,
    karamataBudget := 24, slack := 4 }

example : karamataRefinementWindowReady sampleKaramataRefinementWindow := by
  norm_num [karamataRefinementWindowReady,
    KaramataRefinementWindow.summatoryControlled, sampleKaramataRefinementWindow]


structure HardyLittlewoodKaramataSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HardyLittlewoodKaramataSchemasBudgetCertificate.controlled
    (c : HardyLittlewoodKaramataSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HardyLittlewoodKaramataSchemasBudgetCertificate.budgetControlled
    (c : HardyLittlewoodKaramataSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HardyLittlewoodKaramataSchemasBudgetCertificate.Ready
    (c : HardyLittlewoodKaramataSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HardyLittlewoodKaramataSchemasBudgetCertificate.size
    (c : HardyLittlewoodKaramataSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem hardyLittlewoodKaramataSchemas_budgetCertificate_le_size
    (c : HardyLittlewoodKaramataSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHardyLittlewoodKaramataSchemasBudgetCertificate :
    HardyLittlewoodKaramataSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleHardyLittlewoodKaramataSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [HardyLittlewoodKaramataSchemasBudgetCertificate.controlled,
      sampleHardyLittlewoodKaramataSchemasBudgetCertificate]
  · norm_num [HardyLittlewoodKaramataSchemasBudgetCertificate.budgetControlled,
      sampleHardyLittlewoodKaramataSchemasBudgetCertificate]

example :
    sampleHardyLittlewoodKaramataSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleHardyLittlewoodKaramataSchemasBudgetCertificate.size := by
  apply hardyLittlewoodKaramataSchemas_budgetCertificate_le_size
  constructor
  · norm_num [HardyLittlewoodKaramataSchemasBudgetCertificate.controlled,
      sampleHardyLittlewoodKaramataSchemasBudgetCertificate]
  · norm_num [HardyLittlewoodKaramataSchemasBudgetCertificate.budgetControlled,
      sampleHardyLittlewoodKaramataSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleHardyLittlewoodKaramataSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [HardyLittlewoodKaramataSchemasBudgetCertificate.controlled,
      sampleHardyLittlewoodKaramataSchemasBudgetCertificate]
  · norm_num [HardyLittlewoodKaramataSchemasBudgetCertificate.budgetControlled,
      sampleHardyLittlewoodKaramataSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHardyLittlewoodKaramataSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleHardyLittlewoodKaramataSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List HardyLittlewoodKaramataSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHardyLittlewoodKaramataSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHardyLittlewoodKaramataSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.HardyLittlewoodKaramataSchemas
