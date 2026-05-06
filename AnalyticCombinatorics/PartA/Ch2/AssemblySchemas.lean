import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Assembly schemas for labelled constructions.

The finite data records the component counts of set-like, sequence-like, and
cycle-like labelled constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch2.AssemblySchemas

structure AssemblyData where
  atoms : ℕ
  setBlocks : ℕ
  cycleBlocks : ℕ
deriving DecidableEq, Repr

def componentCount (d : AssemblyData) : ℕ :=
  d.atoms + d.setBlocks + d.cycleBlocks

def nonemptyAssembly (d : AssemblyData) : Prop :=
  0 < componentCount d

theorem componentCount_ge_atoms (d : AssemblyData) :
    d.atoms ≤ componentCount d := by
  unfold componentCount
  omega

theorem atom_positive_nonempty {d : AssemblyData}
    (h : 0 < d.atoms) :
    nonemptyAssembly d := by
  unfold nonemptyAssembly componentCount
  omega

def sampleAssembly : AssemblyData :=
  { atoms := 2, setBlocks := 3, cycleBlocks := 1 }

example : componentCount sampleAssembly = 6 := by
  native_decide

example : nonemptyAssembly sampleAssembly := by
  norm_num [nonemptyAssembly, componentCount, sampleAssembly]

structure AssemblyWindow where
  atoms : ℕ
  setBlocks : ℕ
  sequenceBlocks : ℕ
  cycleBlocks : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AssemblyWindow.blockCount (w : AssemblyWindow) : ℕ :=
  w.setBlocks + w.sequenceBlocks + w.cycleBlocks

def AssemblyWindow.ready (w : AssemblyWindow) : Prop :=
  w.blockCount ≤ w.atoms + w.slack

def AssemblyWindow.hasLabelledAtoms (w : AssemblyWindow) : Prop :=
  0 < w.atoms

def AssemblyWindow.certificate (w : AssemblyWindow) : ℕ :=
  w.atoms + w.setBlocks + w.sequenceBlocks + w.cycleBlocks + w.slack

theorem blockCount_le_certificate (w : AssemblyWindow) :
    w.blockCount ≤ w.certificate := by
  unfold AssemblyWindow.blockCount AssemblyWindow.certificate
  omega

def sampleAssemblyWindow : AssemblyWindow :=
  { atoms := 7, setBlocks := 2, sequenceBlocks := 3, cycleBlocks := 1, slack := 0 }

example : sampleAssemblyWindow.ready := by
  norm_num [sampleAssemblyWindow, AssemblyWindow.ready, AssemblyWindow.blockCount]

example : sampleAssemblyWindow.hasLabelledAtoms := by
  norm_num [sampleAssemblyWindow, AssemblyWindow.hasLabelledAtoms]


structure AssemblySchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AssemblySchemasBudgetCertificate.controlled
    (c : AssemblySchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AssemblySchemasBudgetCertificate.budgetControlled
    (c : AssemblySchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AssemblySchemasBudgetCertificate.Ready
    (c : AssemblySchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AssemblySchemasBudgetCertificate.size
    (c : AssemblySchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem assemblySchemas_budgetCertificate_le_size
    (c : AssemblySchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAssemblySchemasBudgetCertificate :
    AssemblySchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAssemblySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AssemblySchemasBudgetCertificate.controlled,
      sampleAssemblySchemasBudgetCertificate]
  · norm_num [AssemblySchemasBudgetCertificate.budgetControlled,
      sampleAssemblySchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAssemblySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAssemblySchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAssemblySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AssemblySchemasBudgetCertificate.controlled,
      sampleAssemblySchemasBudgetCertificate]
  · norm_num [AssemblySchemasBudgetCertificate.budgetControlled,
      sampleAssemblySchemasBudgetCertificate]

example :
    sampleAssemblySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAssemblySchemasBudgetCertificate.size := by
  apply assemblySchemas_budgetCertificate_le_size
  constructor
  · norm_num [AssemblySchemasBudgetCertificate.controlled,
      sampleAssemblySchemasBudgetCertificate]
  · norm_num [AssemblySchemasBudgetCertificate.budgetControlled,
      sampleAssemblySchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AssemblySchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAssemblySchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAssemblySchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.AssemblySchemas
