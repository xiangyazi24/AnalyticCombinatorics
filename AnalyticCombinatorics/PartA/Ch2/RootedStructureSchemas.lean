import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Rooted structure schemas.

The finite data records atom count, root choices, and symmetry budget for
rooted labelled structures.
-/

namespace AnalyticCombinatorics.PartA.Ch2.RootedStructureSchemas

structure RootedStructureData where
  atomCount : ℕ
  rootChoices : ℕ
  symmetryBudget : ℕ
deriving DecidableEq, Repr

def nonemptyRootedStructure (d : RootedStructureData) : Prop :=
  0 < d.atomCount

def rootChoicesControlled (d : RootedStructureData) : Prop :=
  d.rootChoices ≤ d.atomCount + d.symmetryBudget

def rootedStructureReady (d : RootedStructureData) : Prop :=
  nonemptyRootedStructure d ∧ rootChoicesControlled d

def rootedStructureBudget (d : RootedStructureData) : ℕ :=
  d.atomCount + d.rootChoices + d.symmetryBudget

theorem rootedStructureReady.nonempty {d : RootedStructureData}
    (h : rootedStructureReady d) :
    nonemptyRootedStructure d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem atomCount_le_rootedBudget (d : RootedStructureData) :
    d.atomCount ≤ rootedStructureBudget d := by
  unfold rootedStructureBudget
  omega

def sampleRootedStructure : RootedStructureData :=
  { atomCount := 6, rootChoices := 5, symmetryBudget := 2 }

example : rootedStructureReady sampleRootedStructure := by
  norm_num [rootedStructureReady, nonemptyRootedStructure]
  norm_num [rootChoicesControlled, sampleRootedStructure]

example : rootedStructureBudget sampleRootedStructure = 13 := by
  native_decide

structure RootedStructureWindow where
  atomCount : ℕ
  rootChoices : ℕ
  symmetryBudget : ℕ
  rootingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RootedStructureWindow.rootChoicesControlled (w : RootedStructureWindow) : Prop :=
  w.rootChoices ≤ w.atomCount + w.symmetryBudget + w.slack

def RootedStructureWindow.rootingControlled (w : RootedStructureWindow) : Prop :=
  w.rootingBudget ≤ w.atomCount + w.rootChoices + w.symmetryBudget + w.slack

def rootedStructureWindowReady (w : RootedStructureWindow) : Prop :=
  0 < w.atomCount ∧
    w.rootChoicesControlled ∧
    w.rootingControlled

def RootedStructureWindow.certificate (w : RootedStructureWindow) : ℕ :=
  w.atomCount + w.rootChoices + w.symmetryBudget + w.slack

theorem rootedStructure_rootingBudget_le_certificate {w : RootedStructureWindow}
    (h : rootedStructureWindowReady w) :
    w.rootingBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hrooting⟩
  exact hrooting

def sampleRootedStructureWindow : RootedStructureWindow :=
  { atomCount := 6, rootChoices := 5, symmetryBudget := 2, rootingBudget := 12, slack := 0 }

example : rootedStructureWindowReady sampleRootedStructureWindow := by
  norm_num [rootedStructureWindowReady, RootedStructureWindow.rootChoicesControlled,
    RootedStructureWindow.rootingControlled, sampleRootedStructureWindow]

example : sampleRootedStructureWindow.certificate = 13 := by
  native_decide


structure RootedStructureSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RootedStructureSchemasBudgetCertificate.controlled
    (c : RootedStructureSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RootedStructureSchemasBudgetCertificate.budgetControlled
    (c : RootedStructureSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RootedStructureSchemasBudgetCertificate.Ready
    (c : RootedStructureSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RootedStructureSchemasBudgetCertificate.size
    (c : RootedStructureSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem rootedStructureSchemas_budgetCertificate_le_size
    (c : RootedStructureSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRootedStructureSchemasBudgetCertificate :
    RootedStructureSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRootedStructureSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RootedStructureSchemasBudgetCertificate.controlled,
      sampleRootedStructureSchemasBudgetCertificate]
  · norm_num [RootedStructureSchemasBudgetCertificate.budgetControlled,
      sampleRootedStructureSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRootedStructureSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRootedStructureSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRootedStructureSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RootedStructureSchemasBudgetCertificate.controlled,
      sampleRootedStructureSchemasBudgetCertificate]
  · norm_num [RootedStructureSchemasBudgetCertificate.budgetControlled,
      sampleRootedStructureSchemasBudgetCertificate]

example :
    sampleRootedStructureSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRootedStructureSchemasBudgetCertificate.size := by
  apply rootedStructureSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RootedStructureSchemasBudgetCertificate.controlled,
      sampleRootedStructureSchemasBudgetCertificate]
  · norm_num [RootedStructureSchemasBudgetCertificate.budgetControlled,
      sampleRootedStructureSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RootedStructureSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRootedStructureSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRootedStructureSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.RootedStructureSchemas
