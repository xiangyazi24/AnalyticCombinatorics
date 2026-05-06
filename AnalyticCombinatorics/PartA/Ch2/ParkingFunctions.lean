import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Parking function examples.
-/

namespace AnalyticCombinatorics.PartA.Ch2.ParkingFunctions

structure ParkingWindow where
  carCount : ℕ
  preferenceSlots : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def parkingWindowReady (w : ParkingWindow) : Prop :=
  0 < w.carCount ∧ w.preferenceSlots ≤ w.carCount + w.slack

def parkingWindowBudget (w : ParkingWindow) : ℕ :=
  w.carCount + w.preferenceSlots + w.slack

/-- Parking function counts `(n + 1)^(n - 1)` for small `n`. -/
def parkingFunctionCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 16
  | 4 => 125
  | 5 => 1296
  | 6 => 16807
  | _ => 0

def parkingFunctionFormula (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | k + 1 => (k + 2) ^ k

theorem parkingWindowReady.certificate {w : ParkingWindow}
    (h : parkingWindowReady w) :
    0 < w.carCount ∧ w.preferenceSlots ≤ w.carCount + w.slack ∧
      w.preferenceSlots ≤ parkingWindowBudget w := by
  rcases h with ⟨hcars, hslots⟩
  refine ⟨hcars, hslots, ?_⟩
  unfold parkingWindowBudget
  omega

def sampleParkingWindow : ParkingWindow :=
  { carCount := 5, preferenceSlots := 6, slack := 1 }

example : parkingWindowReady sampleParkingWindow := by
  norm_num [parkingWindowReady, sampleParkingWindow]

example : parkingFunctionCount 0 = 1 := by native_decide
example : parkingFunctionCount 3 = 16 := by native_decide
example : parkingFunctionCount 6 = 16807 := by native_decide
example : parkingFunctionFormula 6 = parkingFunctionCount 6 := by native_decide
example : parkingWindowBudget sampleParkingWindow = 12 := by native_decide

theorem parkingFunctionCount_values_0_to_6 :
    (List.range 7).map parkingFunctionCount =
      [1, 1, 3, 16, 125, 1296, 16807] := by
  native_decide


structure ParkingFunctionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ParkingFunctionsBudgetCertificate.controlled
    (c : ParkingFunctionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ParkingFunctionsBudgetCertificate.budgetControlled
    (c : ParkingFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ParkingFunctionsBudgetCertificate.Ready
    (c : ParkingFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ParkingFunctionsBudgetCertificate.size
    (c : ParkingFunctionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem parkingFunctions_budgetCertificate_le_size
    (c : ParkingFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleParkingFunctionsBudgetCertificate :
    ParkingFunctionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleParkingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [ParkingFunctionsBudgetCertificate.controlled,
      sampleParkingFunctionsBudgetCertificate]
  · norm_num [ParkingFunctionsBudgetCertificate.budgetControlled,
      sampleParkingFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleParkingFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleParkingFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleParkingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [ParkingFunctionsBudgetCertificate.controlled,
      sampleParkingFunctionsBudgetCertificate]
  · norm_num [ParkingFunctionsBudgetCertificate.budgetControlled,
      sampleParkingFunctionsBudgetCertificate]

example :
    sampleParkingFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleParkingFunctionsBudgetCertificate.size := by
  apply parkingFunctions_budgetCertificate_le_size
  constructor
  · norm_num [ParkingFunctionsBudgetCertificate.controlled,
      sampleParkingFunctionsBudgetCertificate]
  · norm_num [ParkingFunctionsBudgetCertificate.budgetControlled,
      sampleParkingFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ParkingFunctionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleParkingFunctionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleParkingFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.ParkingFunctions
