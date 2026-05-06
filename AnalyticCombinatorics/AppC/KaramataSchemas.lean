import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Karamata-style Tauberian schemas.

The file records finite hypothesis bundles for regularly varying tails and
their summatory counterparts.
-/

namespace AnalyticCombinatorics.AppC.KaramataSchemas

structure KaramataData where
  indexNumerator : ℕ
  indexDenominator : ℕ
  monotoneTail : Prop
  slowVariation : Prop
deriving Repr

def positiveIndexDenominator (d : KaramataData) : Prop :=
  0 < d.indexDenominator

def karamataReady (d : KaramataData) : Prop :=
  positiveIndexDenominator d ∧ d.monotoneTail ∧ d.slowVariation

def indexBudget (d : KaramataData) : ℕ :=
  d.indexNumerator + d.indexDenominator

theorem karamataReady.slow {d : KaramataData}
    (h : karamataReady d) :
    d.slowVariation := h.2.2

theorem positiveIndexDenominator_le_budget {d : KaramataData}
    (h : positiveIndexDenominator d) :
    positiveIndexDenominator d ∧ d.indexDenominator ≤ indexBudget d := by
  refine ⟨h, ?_⟩
  unfold indexBudget
  omega

def sampleKaramata : KaramataData :=
  { indexNumerator := 3, indexDenominator := 2, monotoneTail := 2 ≤ 3,
    slowVariation := 3 + 2 = 5 }

example : karamataReady sampleKaramata := by
  norm_num [karamataReady, positiveIndexDenominator, sampleKaramata]

example : indexBudget sampleKaramata = 5 := by
  native_decide

structure KaramataWindow where
  indexNumerator : ℕ
  indexDenominator : ℕ
  slowVariationBudget : ℕ
  tailMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KaramataWindow.indexReady (w : KaramataWindow) : Prop :=
  0 < w.indexDenominator

def KaramataWindow.tailControlled (w : KaramataWindow) : Prop :=
  w.tailMass ≤ (w.indexNumerator + w.indexDenominator) * w.slowVariationBudget + w.slack

def KaramataWindow.ready (w : KaramataWindow) : Prop :=
  w.indexReady ∧ w.tailControlled

def KaramataWindow.certificate (w : KaramataWindow) : ℕ :=
  w.indexNumerator + w.indexDenominator + w.slowVariationBudget + w.tailMass + w.slack

theorem slowVariationBudget_le_certificate (w : KaramataWindow) :
    w.slowVariationBudget ≤ w.certificate := by
  unfold KaramataWindow.certificate
  omega

def sampleKaramataWindow : KaramataWindow :=
  { indexNumerator := 3, indexDenominator := 2, slowVariationBudget := 4,
    tailMass := 12, slack := 0 }

example : sampleKaramataWindow.ready := by
  norm_num [sampleKaramataWindow, KaramataWindow.ready, KaramataWindow.indexReady,
    KaramataWindow.tailControlled]

structure KaramataRefinementWindow where
  numeratorWindow : ℕ
  denominatorWindow : ℕ
  slowWindow : ℕ
  tailWindow : ℕ
  karamataBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KaramataRefinementWindow.tailControlled
    (w : KaramataRefinementWindow) : Prop :=
  w.tailWindow ≤ (w.numeratorWindow + w.denominatorWindow) * w.slowWindow + w.slack

def karamataRefinementWindowReady (w : KaramataRefinementWindow) : Prop :=
  0 < w.denominatorWindow ∧ w.tailControlled ∧
    w.karamataBudget ≤ w.numeratorWindow + w.denominatorWindow + w.tailWindow + w.slack

def KaramataRefinementWindow.certificate
    (w : KaramataRefinementWindow) : ℕ :=
  w.numeratorWindow + w.denominatorWindow + w.slowWindow + w.tailWindow +
    w.karamataBudget + w.slack

theorem karamataRefinement_budget_le_certificate
    (w : KaramataRefinementWindow) :
    w.karamataBudget ≤ w.certificate := by
  unfold KaramataRefinementWindow.certificate
  omega

def sampleKaramataRefinementWindow : KaramataRefinementWindow :=
  { numeratorWindow := 3, denominatorWindow := 2, slowWindow := 4,
    tailWindow := 12, karamataBudget := 18, slack := 1 }

example : karamataRefinementWindowReady sampleKaramataRefinementWindow := by
  norm_num [karamataRefinementWindowReady,
    KaramataRefinementWindow.tailControlled, sampleKaramataRefinementWindow]


structure KaramataSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KaramataSchemasBudgetCertificate.controlled
    (c : KaramataSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def KaramataSchemasBudgetCertificate.budgetControlled
    (c : KaramataSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def KaramataSchemasBudgetCertificate.Ready
    (c : KaramataSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def KaramataSchemasBudgetCertificate.size
    (c : KaramataSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem karamataSchemas_budgetCertificate_le_size
    (c : KaramataSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleKaramataSchemasBudgetCertificate :
    KaramataSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleKaramataSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [KaramataSchemasBudgetCertificate.controlled,
      sampleKaramataSchemasBudgetCertificate]
  · norm_num [KaramataSchemasBudgetCertificate.budgetControlled,
      sampleKaramataSchemasBudgetCertificate]

example :
    sampleKaramataSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleKaramataSchemasBudgetCertificate.size := by
  apply karamataSchemas_budgetCertificate_le_size
  constructor
  · norm_num [KaramataSchemasBudgetCertificate.controlled,
      sampleKaramataSchemasBudgetCertificate]
  · norm_num [KaramataSchemasBudgetCertificate.budgetControlled,
      sampleKaramataSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleKaramataSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [KaramataSchemasBudgetCertificate.controlled,
      sampleKaramataSchemasBudgetCertificate]
  · norm_num [KaramataSchemasBudgetCertificate.budgetControlled,
      sampleKaramataSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleKaramataSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleKaramataSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List KaramataSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleKaramataSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleKaramataSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.KaramataSchemas
