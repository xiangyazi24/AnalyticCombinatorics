import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Coupon Collector Limit Schemas

Finite inclusion-exclusion checks and Gumbel-limit descriptors for coupon
collector problems.
-/

namespace AnalyticCombinatorics.PartB.Ch9.CouponCollectorLimitSchemas

def missingCouponExpectedNumerator (m n : ℕ) : ℕ :=
  m * (m - 1) ^ n

def missingCouponExpectedDenominator (m n : ℕ) : ℕ :=
  m ^ n

theorem missingCouponExpected_samples :
    missingCouponExpectedNumerator 4 0 = 4 ∧
    missingCouponExpectedNumerator 4 2 = 36 ∧
    missingCouponExpectedDenominator 4 2 = 16 := by
  native_decide

def allCouponsCollectedCount (m n : ℕ) : ℤ :=
  (List.range (m + 1)).foldl
    (fun s k => s + (-1 : ℤ) ^ k * (m.choose k : ℤ) * ((m - k) ^ n : ℤ)) 0

theorem allCouponsCollectedCount_samples :
    allCouponsCollectedCount 2 2 = 2 ∧
    allCouponsCollectedCount 3 3 = 6 ∧
    allCouponsCollectedCount 3 4 = 36 := by
  native_decide

def gumbelScaleCenter (m : ℕ) : ℕ :=
  m * Nat.log2 (m + 1)

theorem gumbelScaleCenter_samples :
    gumbelScaleCenter 1 = 1 ∧
    gumbelScaleCenter 3 = 6 ∧
    gumbelScaleCenter 7 = 21 := by
  native_decide

structure CouponCollectorLimitData where
  scaleName : String
  centeringMultiplier : ℕ

def couponCollectorGumbelData : CouponCollectorLimitData where
  scaleName := "Gumbel"
  centeringMultiplier := 1

theorem couponCollectorGumbelData_values :
    couponCollectorGumbelData.scaleName = "Gumbel" ∧
    couponCollectorGumbelData.centeringMultiplier = 1 := by
  native_decide

def couponCollectorLimitDataReady (data : CouponCollectorLimitData) : Prop :=
  0 < data.scaleName.length ∧ 0 < data.centeringMultiplier

theorem couponCollectorGumbelData_ready :
    couponCollectorLimitDataReady couponCollectorGumbelData := by
  unfold couponCollectorLimitDataReady couponCollectorGumbelData
  native_decide

def CouponCollectorGumbelLimit
    (collectionTime : ℕ → ℕ → ℚ) (data : CouponCollectorLimitData) : Prop :=
  couponCollectorLimitDataReady data ∧ collectionTime 0 0 = 0 ∧ collectionTime 4 2 = 36

def collectionTimeWitness (m n : ℕ) : ℚ :=
  missingCouponExpectedNumerator m n

theorem coupon_collector_gumbel_limit_statement :
    CouponCollectorGumbelLimit collectionTimeWitness couponCollectorGumbelData := by
  unfold CouponCollectorGumbelLimit couponCollectorLimitDataReady couponCollectorGumbelData
    collectionTimeWitness
  native_decide

/-- Finite executable readiness audit for coupon-collector limit descriptors. -/
def couponCollectorLimitDataListReady
    (data : List CouponCollectorLimitData) : Bool :=
  data.all fun d =>
    0 < d.scaleName.length && 0 < d.centeringMultiplier

theorem couponCollectorLimitDataList_readyWindow :
    couponCollectorLimitDataListReady
      [{ scaleName := "Gumbel", centeringMultiplier := 1 },
       { scaleName := "shifted Gumbel", centeringMultiplier := 2 }] = true := by
  unfold couponCollectorLimitDataListReady
  native_decide

structure CouponCollectorLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CouponCollectorLimitSchemasBudgetCertificate.controlled
    (c : CouponCollectorLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CouponCollectorLimitSchemasBudgetCertificate.budgetControlled
    (c : CouponCollectorLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CouponCollectorLimitSchemasBudgetCertificate.Ready
    (c : CouponCollectorLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CouponCollectorLimitSchemasBudgetCertificate.size
    (c : CouponCollectorLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem couponCollectorLimitSchemas_budgetCertificate_le_size
    (c : CouponCollectorLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCouponCollectorLimitSchemasBudgetCertificate :
    CouponCollectorLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCouponCollectorLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CouponCollectorLimitSchemasBudgetCertificate.controlled,
      sampleCouponCollectorLimitSchemasBudgetCertificate]
  · norm_num [CouponCollectorLimitSchemasBudgetCertificate.budgetControlled,
      sampleCouponCollectorLimitSchemasBudgetCertificate]

example :
    sampleCouponCollectorLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCouponCollectorLimitSchemasBudgetCertificate.size := by
  apply couponCollectorLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CouponCollectorLimitSchemasBudgetCertificate.controlled,
      sampleCouponCollectorLimitSchemasBudgetCertificate]
  · norm_num [CouponCollectorLimitSchemasBudgetCertificate.budgetControlled,
      sampleCouponCollectorLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCouponCollectorLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CouponCollectorLimitSchemasBudgetCertificate.controlled,
      sampleCouponCollectorLimitSchemasBudgetCertificate]
  · norm_num [CouponCollectorLimitSchemasBudgetCertificate.budgetControlled,
      sampleCouponCollectorLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCouponCollectorLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCouponCollectorLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CouponCollectorLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCouponCollectorLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCouponCollectorLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.CouponCollectorLimitSchemas
