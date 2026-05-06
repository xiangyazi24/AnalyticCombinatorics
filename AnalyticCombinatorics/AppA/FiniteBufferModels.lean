import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite buffer models.

Buffers are represented by lists of packet sizes.  The definitions record
occupancy, capacity, and overflow calculations.
-/

namespace AnalyticCombinatorics.AppA.FiniteBufferModels

def bufferOccupancy (xs : List ℕ) : ℕ :=
  xs.sum

def bufferItems (xs : List ℕ) : ℕ :=
  xs.length

def withinBufferCapacity (xs : List ℕ) (capacity : ℕ) : Prop :=
  bufferOccupancy xs ≤ capacity

def overflowAmount (xs : List ℕ) (capacity : ℕ) : ℕ :=
  bufferOccupancy xs - capacity

theorem bufferOccupancy_cons (x : ℕ) (xs : List ℕ) :
    bufferOccupancy (x :: xs) = x + bufferOccupancy xs := by
  simp [bufferOccupancy]

theorem bufferItems_cons (x : ℕ) (xs : List ℕ) :
    bufferItems (x :: xs) = bufferItems xs + 1 := by
  simp [bufferItems]

theorem withinBufferCapacity_mono {xs : List ℕ} {a b : ℕ}
    (h : withinBufferCapacity xs a) (hab : a ≤ b) :
    withinBufferCapacity xs b := by
  unfold withinBufferCapacity at *
  omega

def sampleBuffer : List ℕ :=
  [2, 5, 1]

example : bufferOccupancy sampleBuffer = 8 := by
  native_decide

example : bufferItems sampleBuffer = 3 := by
  native_decide

example : withinBufferCapacity sampleBuffer 10 := by
  norm_num [withinBufferCapacity, bufferOccupancy, sampleBuffer]

structure BufferWindow where
  items : ℕ
  occupancy : ℕ
  capacity : ℕ
  overflow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BufferWindow.capacityReady (w : BufferWindow) : Prop :=
  w.occupancy ≤ w.capacity + w.overflow + w.slack

def BufferWindow.itemControlled (w : BufferWindow) : Prop :=
  w.items ≤ w.occupancy + w.slack

def BufferWindow.ready (w : BufferWindow) : Prop :=
  w.capacityReady ∧ w.itemControlled

def BufferWindow.certificate (w : BufferWindow) : ℕ :=
  w.items + w.occupancy + w.capacity + w.overflow + w.slack

theorem overflow_le_certificate (w : BufferWindow) :
    w.overflow ≤ w.certificate := by
  unfold BufferWindow.certificate
  omega

def sampleBufferWindow : BufferWindow :=
  { items := 3, occupancy := 8, capacity := 10, overflow := 0, slack := 0 }

example : sampleBufferWindow.ready := by
  norm_num [sampleBufferWindow, BufferWindow.ready, BufferWindow.capacityReady,
    BufferWindow.itemControlled]


structure FiniteBufferModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteBufferModelsBudgetCertificate.controlled
    (c : FiniteBufferModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteBufferModelsBudgetCertificate.budgetControlled
    (c : FiniteBufferModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteBufferModelsBudgetCertificate.Ready
    (c : FiniteBufferModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteBufferModelsBudgetCertificate.size
    (c : FiniteBufferModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteBufferModels_budgetCertificate_le_size
    (c : FiniteBufferModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteBufferModelsBudgetCertificate :
    FiniteBufferModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteBufferModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteBufferModelsBudgetCertificate.controlled,
      sampleFiniteBufferModelsBudgetCertificate]
  · norm_num [FiniteBufferModelsBudgetCertificate.budgetControlled,
      sampleFiniteBufferModelsBudgetCertificate]

example :
    sampleFiniteBufferModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteBufferModelsBudgetCertificate.size := by
  apply finiteBufferModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteBufferModelsBudgetCertificate.controlled,
      sampleFiniteBufferModelsBudgetCertificate]
  · norm_num [FiniteBufferModelsBudgetCertificate.budgetControlled,
      sampleFiniteBufferModelsBudgetCertificate]

/-- Finite executable readiness audit for finite-buffer certificates. -/
def finiteBufferModelsBudgetCertificateListReady
    (data : List FiniteBufferModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteBufferModelsBudgetCertificateList_readyWindow :
    finiteBufferModelsBudgetCertificateListReady
      [sampleFiniteBufferModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold finiteBufferModelsBudgetCertificateListReady
    sampleFiniteBufferModelsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteBufferModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteBufferModelsBudgetCertificate.controlled,
      sampleFiniteBufferModelsBudgetCertificate]
  · norm_num [FiniteBufferModelsBudgetCertificate.budgetControlled,
      sampleFiniteBufferModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteBufferModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteBufferModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FiniteBufferModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteBufferModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFiniteBufferModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FiniteBufferModels
