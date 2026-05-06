import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random planar map limit schema bookkeeping.

The finite data records face, edge, and variance budgets for planar-map
limit laws.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomPlanarMapLimitSchemas

structure RandomPlanarMapData where
  faceBudget : ℕ
  edgeBudget : ℕ
  varianceBudget : ℕ
deriving DecidableEq, Repr

def positiveFaceBudget (d : RandomPlanarMapData) : Prop :=
  0 < d.faceBudget

def positiveVarianceBudget (d : RandomPlanarMapData) : Prop :=
  0 < d.varianceBudget

def randomPlanarMapReady (d : RandomPlanarMapData) : Prop :=
  positiveFaceBudget d ∧ positiveVarianceBudget d

def planarMapBudget (d : RandomPlanarMapData) : ℕ :=
  d.faceBudget + d.edgeBudget + d.varianceBudget

theorem randomPlanarMapReady.faces {d : RandomPlanarMapData}
    (h : randomPlanarMapReady d) :
    positiveFaceBudget d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem faceBudget_le_total (d : RandomPlanarMapData) :
    d.faceBudget ≤ planarMapBudget d := by
  unfold planarMapBudget
  omega

def samplePlanarMap : RandomPlanarMapData :=
  { faceBudget := 6, edgeBudget := 9, varianceBudget := 4 }

example : randomPlanarMapReady samplePlanarMap := by
  norm_num [randomPlanarMapReady, positiveFaceBudget, positiveVarianceBudget, samplePlanarMap]

example : planarMapBudget samplePlanarMap = 19 := by
  native_decide

/-- Finite executable readiness audit for random planar-map data. -/
def randomPlanarMapDataListReady
    (data : List RandomPlanarMapData) : Bool :=
  data.all fun d =>
    0 < d.faceBudget &&
      0 < d.varianceBudget &&
        d.edgeBudget ≤ 3 * d.faceBudget

theorem randomPlanarMapDataList_readyWindow :
    randomPlanarMapDataListReady
      [{ faceBudget := 4, edgeBudget := 6, varianceBudget := 2 },
       { faceBudget := 6, edgeBudget := 9, varianceBudget := 4 }] = true := by
  unfold randomPlanarMapDataListReady
  native_decide

structure RandomPlanarMapWindow where
  faceBudget : ℕ
  edgeBudget : ℕ
  varianceBudget : ℕ
  mapBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomPlanarMapWindow.edgeControlled (w : RandomPlanarMapWindow) : Prop :=
  w.edgeBudget ≤ 3 * w.faceBudget + w.slack

def RandomPlanarMapWindow.mapControlled (w : RandomPlanarMapWindow) : Prop :=
  w.mapBudget ≤ w.faceBudget + w.edgeBudget + w.varianceBudget + w.slack

def randomPlanarMapWindowReady (w : RandomPlanarMapWindow) : Prop :=
  0 < w.faceBudget ∧
    0 < w.varianceBudget ∧
    w.edgeControlled ∧
    w.mapControlled

def RandomPlanarMapWindow.certificate (w : RandomPlanarMapWindow) : ℕ :=
  w.faceBudget + w.edgeBudget + w.varianceBudget + w.slack

theorem randomPlanarMap_mapBudget_le_certificate {w : RandomPlanarMapWindow}
    (h : randomPlanarMapWindowReady w) :
    w.mapBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hmap⟩
  exact hmap

def sampleRandomPlanarMapWindow : RandomPlanarMapWindow :=
  { faceBudget := 6, edgeBudget := 9, varianceBudget := 4, mapBudget := 17, slack := 0 }

example : randomPlanarMapWindowReady sampleRandomPlanarMapWindow := by
  norm_num [randomPlanarMapWindowReady, RandomPlanarMapWindow.edgeControlled,
    RandomPlanarMapWindow.mapControlled, sampleRandomPlanarMapWindow]

example : sampleRandomPlanarMapWindow.certificate = 19 := by
  native_decide


structure RandomPlanarMapLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomPlanarMapLimitSchemasBudgetCertificate.controlled
    (c : RandomPlanarMapLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomPlanarMapLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomPlanarMapLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomPlanarMapLimitSchemasBudgetCertificate.Ready
    (c : RandomPlanarMapLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomPlanarMapLimitSchemasBudgetCertificate.size
    (c : RandomPlanarMapLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomPlanarMapLimitSchemas_budgetCertificate_le_size
    (c : RandomPlanarMapLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomPlanarMapLimitSchemasBudgetCertificate :
    RandomPlanarMapLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRandomPlanarMapLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomPlanarMapLimitSchemasBudgetCertificate.controlled,
      sampleRandomPlanarMapLimitSchemasBudgetCertificate]
  · norm_num [RandomPlanarMapLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomPlanarMapLimitSchemasBudgetCertificate]

example :
    sampleRandomPlanarMapLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomPlanarMapLimitSchemasBudgetCertificate.size := by
  apply randomPlanarMapLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomPlanarMapLimitSchemasBudgetCertificate.controlled,
      sampleRandomPlanarMapLimitSchemasBudgetCertificate]
  · norm_num [RandomPlanarMapLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomPlanarMapLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRandomPlanarMapLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomPlanarMapLimitSchemasBudgetCertificate.controlled,
      sampleRandomPlanarMapLimitSchemasBudgetCertificate]
  · norm_num [RandomPlanarMapLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomPlanarMapLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomPlanarMapLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomPlanarMapLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RandomPlanarMapLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomPlanarMapLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomPlanarMapLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomPlanarMapLimitSchemas
