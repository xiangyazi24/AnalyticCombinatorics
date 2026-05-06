import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# A roadmap to rational and meromorphic asymptotics
-/

namespace AnalyticCombinatorics.PartB.Ch5.RoadmapToRationalAndMeromorphicAsymptotics

/-- Pole data for rational/meromorphic transfer. -/
structure PoleData where
  radiusInv : ℕ
  order : ℕ
  residue : ℕ
deriving DecidableEq, Repr

def PoleData.ready (p : PoleData) : Prop :=
  0 < p.radiusInv ∧ 0 < p.order

def poleTransferCoeff (p : PoleData) (n : ℕ) : ℕ :=
  p.residue * (n + p.order - 1).choose (p.order - 1) * p.radiusInv ^ n

def simpleUnitPole : PoleData :=
  { radiusInv := 2, order := 1, residue := 1 }

theorem simpleUnitPole_ready :
    simpleUnitPole.ready := by
  norm_num [PoleData.ready, simpleUnitPole]

theorem poleTransferCoeff_simpleUnit (n : ℕ) :
    poleTransferCoeff simpleUnitPole n = 2 ^ n := by
  simp [poleTransferCoeff, simpleUnitPole]

structure RationalMeromorphicRoadmapWindow where
  poleWindow : ℕ
  residueWindow : ℕ
  transferWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RationalMeromorphicRoadmapWindow.ready
    (w : RationalMeromorphicRoadmapWindow) : Prop :=
  0 < w.poleWindow ∧
    w.transferWindow ≤ w.poleWindow + w.residueWindow + w.slack

def sampleRationalMeromorphicRoadmapWindow :
    RationalMeromorphicRoadmapWindow :=
  { poleWindow := 3, residueWindow := 4, transferWindow := 7, slack := 0 }

example : sampleRationalMeromorphicRoadmapWindow.ready := by
  norm_num [RationalMeromorphicRoadmapWindow.ready,
    sampleRationalMeromorphicRoadmapWindow]

structure RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate where
  poleWindow : ℕ
  residueWindow : ℕ
  transferWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.controlled
    (c : RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate) : Prop :=
  0 < c.poleWindow ∧
    c.transferWindow ≤ c.poleWindow + c.residueWindow + c.slack

def RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.budgetControlled
    (c : RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.poleWindow + c.residueWindow + c.transferWindow + c.slack

def RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.Ready
    (c : RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.size
    (c : RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate) : ℕ :=
  c.poleWindow + c.residueWindow + c.transferWindow + c.slack

def sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate :
    RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate :=
  { poleWindow := 3
    residueWindow := 4
    transferWindow := 7
    certificateBudgetWindow := 15
    slack := 1 }

example :
    RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.Ready
      sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate := by
  constructor
  · norm_num
      [RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.controlled,
        sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate]
  · norm_num
      [RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.budgetControlled,
        sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate]

theorem budgetCertificate_le_size
    (c : RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

theorem sampleBudgetCertificate_le_size :
    sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.size := by
  have h : sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.Ready := by
    constructor
    · norm_num [RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.controlled,
        sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate]
    · norm_num [RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.budgetControlled,
        sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate]
  exact h.2

def budgetCertificateListReady
    (data : List RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate_ready :
    sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.controlled,
        sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate]
  · norm_num
      [RoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.budgetControlled,
        sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate.Ready :=
  sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate_ready

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate] =
        true := by
  unfold budgetCertificateListReady
    sampleRoadmapToRationalAndMeromorphicAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.RoadmapToRationalAndMeromorphicAsymptotics
