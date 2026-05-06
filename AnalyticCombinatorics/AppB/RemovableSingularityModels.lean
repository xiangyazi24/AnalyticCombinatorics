import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Removable-singularity bookkeeping.

Bounded punctured neighborhoods are represented by finite radius and bound
budgets.
-/

namespace AnalyticCombinatorics.AppB.RemovableSingularityModels

structure RemovableDatum where
  puncturedRadius : ℕ
  localBound : ℕ
  extensionBudget : ℕ
deriving DecidableEq, Repr

def positivePuncturedRadius (d : RemovableDatum) : Prop :=
  0 < d.puncturedRadius

def locallyBounded (d : RemovableDatum) : Prop :=
  0 < d.localBound

def removableReady (d : RemovableDatum) : Prop :=
  positivePuncturedRadius d ∧ locallyBounded d

def removableComplexity (d : RemovableDatum) : ℕ :=
  d.puncturedRadius + d.localBound + d.extensionBudget

theorem removableReady.bound {d : RemovableDatum}
    (h : removableReady d) :
    positivePuncturedRadius d ∧ locallyBounded d ∧
      d.puncturedRadius ≤ removableComplexity d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold removableComplexity
  omega

theorem radius_le_complexity (d : RemovableDatum) :
    d.puncturedRadius ≤ removableComplexity d := by
  unfold removableComplexity
  omega

def sampleRemovable : RemovableDatum :=
  { puncturedRadius := 3, localBound := 6, extensionBudget := 2 }

example : removableReady sampleRemovable := by
  norm_num [removableReady, positivePuncturedRadius, locallyBounded, sampleRemovable]

example : removableComplexity sampleRemovable = 11 := by
  native_decide

structure RemovableWindow where
  radiusWindow : ℕ
  boundWindow : ℕ
  extensionWindow : ℕ
  removableBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RemovableWindow.extensionControlled (w : RemovableWindow) : Prop :=
  w.extensionWindow ≤ w.radiusWindow + w.boundWindow + w.slack

def removableWindowReady (w : RemovableWindow) : Prop :=
  0 < w.radiusWindow ∧ 0 < w.boundWindow ∧ w.extensionControlled ∧
    w.removableBudget ≤ w.radiusWindow + w.boundWindow + w.extensionWindow + w.slack

def RemovableWindow.certificate (w : RemovableWindow) : ℕ :=
  w.radiusWindow + w.boundWindow + w.extensionWindow + w.removableBudget + w.slack

theorem removable_removableBudget_le_certificate (w : RemovableWindow) :
    w.removableBudget ≤ w.certificate := by
  unfold RemovableWindow.certificate
  omega

def sampleRemovableWindow : RemovableWindow :=
  { radiusWindow := 3, boundWindow := 6, extensionWindow := 2, removableBudget := 12, slack := 1 }

example : removableWindowReady sampleRemovableWindow := by
  norm_num [removableWindowReady, RemovableWindow.extensionControlled, sampleRemovableWindow]


structure RemovableSingularityModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RemovableSingularityModelsBudgetCertificate.controlled
    (c : RemovableSingularityModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RemovableSingularityModelsBudgetCertificate.budgetControlled
    (c : RemovableSingularityModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RemovableSingularityModelsBudgetCertificate.Ready
    (c : RemovableSingularityModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RemovableSingularityModelsBudgetCertificate.size
    (c : RemovableSingularityModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem removableSingularityModels_budgetCertificate_le_size
    (c : RemovableSingularityModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRemovableSingularityModelsBudgetCertificate :
    RemovableSingularityModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRemovableSingularityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [RemovableSingularityModelsBudgetCertificate.controlled,
      sampleRemovableSingularityModelsBudgetCertificate]
  · norm_num [RemovableSingularityModelsBudgetCertificate.budgetControlled,
      sampleRemovableSingularityModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRemovableSingularityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleRemovableSingularityModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRemovableSingularityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [RemovableSingularityModelsBudgetCertificate.controlled,
      sampleRemovableSingularityModelsBudgetCertificate]
  · norm_num [RemovableSingularityModelsBudgetCertificate.budgetControlled,
      sampleRemovableSingularityModelsBudgetCertificate]

example :
    sampleRemovableSingularityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleRemovableSingularityModelsBudgetCertificate.size := by
  apply removableSingularityModels_budgetCertificate_le_size
  constructor
  · norm_num [RemovableSingularityModelsBudgetCertificate.controlled,
      sampleRemovableSingularityModelsBudgetCertificate]
  · norm_num [RemovableSingularityModelsBudgetCertificate.budgetControlled,
      sampleRemovableSingularityModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RemovableSingularityModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRemovableSingularityModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRemovableSingularityModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.RemovableSingularityModels
