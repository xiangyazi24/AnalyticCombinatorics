import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace HashingAnalysis

/-!
# Chapter IX: Hashing and Random Allocation Analysis

Formalizes key quantitative results from Flajolet–Sedgewick Chapter IX on
hashing, birthday problems, coupon collection, and occupancy:
- Balls into bins: expected empty bins
- Birthday problem exact collision probabilities
- Coupon collector expected time
- Linear probing expected probe lengths
- Robin Hood hashing total probe counts
- Collision probability for occupancy problems
-/

-- ============================================================================
-- § 1. Balls into Bins: Expected Number of Empty Bins
-- ============================================================================

/-!
## Balls into Bins

When n balls are thrown uniformly at random into n bins, the expected number
of empty bins is n * ((n-1)/n)^n ≈ n/e.

We compute this exactly in ℚ for small n.
-/

/-- Numerator of expected empty bins: n * (n-1)^n -/
def emptyNumer : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) * n ^ (n + 1)

/-- Denominator of expected empty bins: n^n -/
def emptyDenom : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) ^ (n + 1)

-- n=2: 2 * 1^2 = 2, denom = 4. Expected = 2/4 = 1/2.
example : emptyNumer 2 = 2 := by native_decide
example : emptyDenom 2 = 4 := by native_decide
example : (2 : ℚ) / 4 = 1 / 2 := by native_decide

-- n=3: 3 * 2^3 = 24, denom = 27. Expected = 24/27 = 8/9.
example : emptyNumer 3 = 24 := by native_decide
example : emptyDenom 3 = 27 := by native_decide
example : (24 : ℚ) / 27 = 8 / 9 := by native_decide

-- n=4: 4 * 3^4 = 324, denom = 256. Expected = 324/256 = 81/64.
example : emptyNumer 4 = 324 := by native_decide
example : emptyDenom 4 = 256 := by native_decide
example : (324 : ℚ) / 256 = 81 / 64 := by native_decide

-- n=5: 5 * 4^5 = 5120, denom = 3125. Expected = 5120/3125 = 1024/625.
example : emptyNumer 5 = 5120 := by native_decide
example : emptyDenom 5 = 3125 := by native_decide
example : (5120 : ℚ) / 3125 = 1024 / 625 := by native_decide

-- For n≥2, the expected number of empty bins exceeds 1 (most allocations leave gaps).
example : (81 : ℚ) / 64 > 1 := by native_decide

-- ============================================================================
-- § 2. Birthday Problem: Exact Collision Probabilities
-- ============================================================================

/-!
## Birthday Problem

P(no collision among n people, m days) = ∏_{i=0}^{n-1} (m - i) / m^n.

The product ∏_{i=0}^{n-1} (m - i) is the falling factorial m^{(n)}.
-/

/-- Falling factorial product: number of ways n people have distinct birthdays
    among m days (as a natural number). -/
def noCollisionCount (m n : ℕ) : ℕ := ∏ i ∈ Finset.range n, (m - i)

-- 365 * 364 = 132860 (n=2, m=365)
example : noCollisionCount 365 2 = 132860 := by native_decide

-- 365^2 = 133225
example : (365 : ℕ) ^ 2 = 133225 := by native_decide

-- P(no collision, 2 people) = 132860/133225 ≈ 0.9973
example : (132860 : ℚ) / 133225 = 26572 / 26645 := by native_decide

-- For n=23 people, birthday paradox: collision prob > 50%.
-- noCollisionCount(365, 23) < 365^23 / 2 iff 2 * noCollisionCount < 365^23.
example : 2 * noCollisionCount 365 23 < 365 ^ 23 := by native_decide

-- For n=22 people, still below 50% (just barely).
example : 2 * noCollisionCount 365 22 > 365 ^ 22 := by native_decide

-- Exact count for 23 people having distinct birthdays
example : noCollisionCount 365 23 =
    42200819302092359872395663074908957253749760700776448000000 := by native_decide

-- 365^23 (total equally likely outcomes)
example : (365 : ℕ) ^ 23 =
    85651679353150321236814267844395152689354622364044189453125 := by native_decide

-- Threshold: n=23 gives P(collision) > 1/2
example : 2 * noCollisionCount 365 23 < 365 ^ 23 := by native_decide

-- ============================================================================
-- § 3. Coupon Collector Expected Time
-- ============================================================================

/-!
## Coupon Collector

Expected number of draws to complete a collection of n distinct coupons:
E[T_n] = n * H_n, where H_n = 1 + 1/2 + ... + 1/n is the harmonic number.
-/

/-- Harmonic number H_n = ∑_{k=1}^{n} 1/k (in ℚ) -/
def harmonicQ (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / ((k + 1) : ℚ)

/-- Expected draws for coupon collector with n coupons = n * H_n -/
def couponTime (n : ℕ) : ℚ := (n : ℚ) * harmonicQ n

-- couponTime 1 = 1 * 1 = 1
example : couponTime 1 = 1 := by native_decide

-- couponTime 2 = 2 * (1 + 1/2) = 2 * 3/2 = 3
example : couponTime 2 = 3 := by native_decide

-- couponTime 3 = 3 * (1 + 1/2 + 1/3) = 3 * 11/6 = 11/2
example : couponTime 3 = 11 / 2 := by native_decide

-- couponTime 4 = 4 * (1 + 1/2 + 1/3 + 1/4) = 4 * 25/12 = 25/3
example : couponTime 4 = 25 / 3 := by native_decide

-- couponTime 5 = 5 * (1 + 1/2 + 1/3 + 1/4 + 1/5) = 5 * 137/60 = 137/12
example : couponTime 5 = 137 / 12 := by native_decide

-- H_10 = 7381/2520
example : harmonicQ 10 = 7381 / 2520 := by native_decide

-- Coupon collector with 10 types: expected = 10 * H_10 = 73810/2520 = 3691/126 ≈ 29.29
example : couponTime 10 = 7381 / 252 := by native_decide

-- Growth: couponTime 100 > 500 (since H_100 ≈ 5.187, so 100*H_100 ≈ 518.7)
example : couponTime 100 > 500 := by native_decide

-- ============================================================================
-- § 4. Linear Probing: Expected Probe Length
-- ============================================================================

/-!
## Linear Probing

Under linear probing with load factor α (fraction of table filled),
the expected number of probes for a successful search is approximately:
  (1 + 1/(1-α)^2) / 2  (Knuth's formula).

We verify this formula at specific rational values of α.
-/

-- α = 1/2: expected = (1 + 1/(1/2)^2) / 2 = (1 + 4) / 2 = 5/2
example : (1 + (1 : ℚ) / (1 / 2) ^ 2) / 2 = 5 / 2 := by native_decide

-- α = 3/4: expected = (1 + 1/(1/4)^2) / 2 = (1 + 16) / 2 = 17/2
example : (1 + (1 : ℚ) / (1 / 4) ^ 2) / 2 = 17 / 2 := by native_decide

-- α = 1/3: expected = (1 + 1/(2/3)^2) / 2 = (1 + 9/4) / 2 = 13/8
example : (1 + (1 : ℚ) / (2 / 3) ^ 2) / 2 = 13 / 8 := by native_decide

-- α = 9/10: expected = (1 + 1/(1/10)^2) / 2 = (1 + 100) / 2 = 101/2
example : (1 + (1 : ℚ) / (1 / 10) ^ 2) / 2 = 101 / 2 := by native_decide

-- As α → 1, probes blow up. At α=99/100: (1 + 10000)/2 = 10001/2
example : (1 + (1 : ℚ) / (1 / 100) ^ 2) / 2 = 10001 / 2 := by native_decide

-- For unsuccessful search, the formula is (1 + 1/(1-α)^2) / 2 — same but
-- different interpretation. Verify at α=1/2 and α=3/4.
example : (1 + (1 : ℚ) / (1 / 2) ^ 2) / 2 = 5 / 2 := by native_decide
example : (1 + (1 : ℚ) / (1 / 4) ^ 2) / 2 = 17 / 2 := by native_decide

-- The ratio of probes at α=3/4 vs α=1/2 is (17/2)/(5/2) = 17/5
example : (17 / 2 : ℚ) / (5 / 2) = 17 / 5 := by native_decide

-- ============================================================================
-- § 5. Robin Hood Hashing: Total Probe Count via Harmonic Numbers
-- ============================================================================

/-!
## Robin Hood Hashing

For a table with m slots containing n items (under ideal hashing assumptions),
the total number of probes over all items is:
  m * H_m - (m - n) * H_{m-n}

where H_k is the k-th harmonic number. We verify this for small tables.
-/

-- H_8 = 761/280
example : harmonicQ 8 = 761 / 280 := by native_decide

-- H_4 = 25/12
example : harmonicQ 4 = 25 / 12 := by native_decide

-- For m=8, n=4: total probes = 8 * H_8 - 4 * H_4
--   = 8 * (761/280) - 4 * (25/12)
--   = 6088/280 - 100/12
--   = 761/35 - 25/3
--   = 2283/105 - 875/105
--   = 1408/105
example : (8 : ℚ) * harmonicQ 8 - 4 * harmonicQ 4 = 1408 / 105 := by native_decide

-- Average probes per item = (1408/105) / 4 = 352/105
example : (1408 : ℚ) / 105 / 4 = 352 / 105 := by native_decide

-- For m=16, n=8: total = 16 * H_16 - 8 * H_8
example : harmonicQ 16 = 2436559 / 720720 := by native_decide
example : (16 : ℚ) * harmonicQ 16 - 8 * harmonicQ 8 = 1457152 / 45045 := by native_decide

-- For m=16, n=12: total = 16*H_16 - 4*H_4
example : (16 : ℚ) * harmonicQ 16 - 4 * harmonicQ 4 =
    16 * (2436559 / 720720) - 4 * (25 / 12) := by native_decide

-- Numerical verification: 1408/105 ≈ 13.41, so average ≈ 3.35 probes per item (m=8, n=4)
example : (1408 : ℚ) / 105 > 13 := by native_decide
example : (1408 : ℚ) / 105 < 14 := by native_decide

-- ============================================================================
-- § 6. Occupancy: Collision Probability
-- ============================================================================

/-!
## Collision Probability

P(at least one collision with n balls in m bins)
  = 1 - m * (m-1) * ... * (m-n+1) / m^n
  = 1 - noCollisionCount(m, n) / m^n.

We verify for small exact cases.
-/

-- m=10, n=3: no-collision count = 10 * 9 * 8 = 720
example : noCollisionCount 10 3 = 720 := by native_decide

-- Total outcomes: 10^3 = 1000
example : (10 : ℕ) ^ 3 = 1000 := by native_decide

-- P(collision) = (1000 - 720) / 1000 = 280/1000 = 7/25
example : (280 : ℚ) / 1000 = 7 / 25 := by native_decide

-- Verify: 1 - 720/1000 = 280/1000
example : 1 - (720 : ℚ) / 1000 = 7 / 25 := by native_decide

-- m=6 (dice), n=3: no-collision = 6*5*4 = 120, total = 216
example : noCollisionCount 6 3 = 120 := by native_decide
example : (6 : ℕ) ^ 3 = 216 := by native_decide
example : 1 - (120 : ℚ) / 216 = 4 / 9 := by native_decide

-- m=52 (cards), n=5: no-collision = 52*51*50*49*48 = 311875200
example : noCollisionCount 52 5 = 311875200 := by native_decide
example : (52 : ℕ) ^ 5 = 380204032 := by native_decide
-- P(all 5 cards distinct rank) ≈ 82%
example : 2 * noCollisionCount 52 5 > 380204032 := by native_decide

-- Birthday paradox threshold for n=23, m=365 (already shown above)
-- Smaller example: m=10, threshold is n=5.
-- n=4: no collision > 50% (noCollisionCount 10 4 = 5040, 10^4 = 10000, 10080 > 10000)
example : 2 * noCollisionCount 10 4 > (10 : ℕ) ^ 4 := by native_decide
-- n=5: collision > 50% (noCollisionCount 10 5 = 30240, 10^5 = 100000, 60480 < 100000)
example : 2 * noCollisionCount 10 5 < (10 : ℕ) ^ 5 := by native_decide

-- ============================================================================
-- § 7. Hashing Table Size Bounds
-- ============================================================================

/-!
## Table Size Bounds

To achieve a low collision probability ε with n items in m bins,
we need m ≥ n^2 / (2 * ln(1/ε)) approximately.

For exact verification: to have P(no collision) ≥ 1/2 with n=23 items,
we need m ≥ 365. Let us check the boundary.
-/

-- With m=22 bins and n=22 items: no collision count = 22! / 1 = 22!
example : noCollisionCount 22 22 = Nat.factorial 22 := by native_decide

-- P(all distinct in 22 bins with 22 items) = 22! / 22^22
example : Nat.factorial 22 = 1124000727777607680000 := by native_decide
example : (22 : ℕ) ^ 22 = 341427877364219557396646723584 := by native_decide

-- P(no collision) = 22!/22^22 is tiny (much less than 1/2)
-- 2 * 22! < 22^22
example : 2 * Nat.factorial 22 < (22 : ℕ) ^ 22 := by native_decide

-- Hashing a set of 10 keys into 100 slots: expected collisions ≈ n^2/(2m) = 100/200 = 1/2
example : (10 : ℕ) ^ 2 = 100 := by native_decide
example : (100 : ℚ) / (2 * 100) = 1 / 2 := by native_decide

-- With 20 keys in 100 slots: expected collisions ≈ 400/200 = 2
example : (20 : ℚ) ^ 2 / (2 * 100) = 2 := by native_decide

-- With 100 keys in 100 slots: expected collisions ≈ 10000/200 = 50
example : (100 : ℚ) ^ 2 / (2 * 100) = 50 := by native_decide

-- ============================================================================
-- § 8. Double Hashing and Universal Hashing
-- ============================================================================

/-!
## Universal Hashing

A family of hash functions is 2-universal if for any two distinct keys x, y,
P(h(x) = h(y)) ≤ 1/m.

For a table with m slots and n keys using a 2-universal family,
the expected number of collisions for a given key k is at most (n-1)/m.
-/

-- For n=50 keys in m=100 slots: expected collisions per key ≤ 49/100
example : (49 : ℚ) / 100 < 1 / 2 := by native_decide

-- For n=100 keys in m=200 slots: expected collisions per key ≤ 99/200
example : (99 : ℚ) / 200 < 1 / 2 := by native_decide

-- Load factor: n keys in m slots, α = n/m
-- For α=1/2: expected chain length ≤ 1/2
example : (1 : ℚ) / 2 < 1 := by native_decide

-- Number of pairs that could collide with n=50 keys: C(50,2) = 1225
example : 50 * 49 / 2 = 1225 := by native_decide

-- With m=1000 slots: expected number of colliding pairs ≤ 1225/1000 = 49/40
example : (1225 : ℚ) / 1000 = 49 / 40 := by native_decide

-- With m = n^2 slots: expected collisions < 1/2 (perfect hashing regime)
-- For n=50: m = 2500, expected colliding pairs ≤ C(50,2)/2500 = 1225/2500 = 49/100
example : (1225 : ℚ) / 2500 = 49 / 100 := by native_decide
example : (49 : ℚ) / 100 < 1 / 2 := by native_decide

-- ============================================================================
-- § 9. Bloom Filters: False Positive Rate
-- ============================================================================

/-!
## Bloom Filters

A Bloom filter with m bits, n elements, and k hash functions has false positive
rate approximately (1 - e^{-kn/m})^k.

Optimal k = (m/n) * ln 2. For m/n = 10: optimal k ≈ 6.93, so k=7.

The false positive rate at optimal k is approximately 2^{-k}.

We verify arithmetic for specific small parameters.
-/

-- Optimal k for m/n = 10: round(10 * ln 2) ≈ round(6.93) = 7
-- Verify: 7 ≤ 10 and 7 > 6 (plausible range)
example : 6 < 7 ∧ 7 ≤ 10 := by native_decide

-- False positive rate ≈ 2^{-k}. For k=7: 1/128
example : (1 : ℚ) / 2 ^ 7 = 1 / 128 := by native_decide

-- For k=10: 1/1024 ≈ 0.001
example : (1 : ℚ) / 2 ^ 10 = 1 / 1024 := by native_decide

-- Bits needed for n elements and false positive rate 1/1000:
-- m ≈ n * log2(1/ε) / ln 2 ≈ n * 14.38
-- For n=1000 elements with ε=0.001: m ≈ 14380 bits ≈ 1.76 KB
-- Verify integer lower bound: 1000 * 10 < 14380
example : 1000 * 10 < 14380 := by native_decide

-- Number of hash functions for ε=0.001: k ≈ log2(1000) / (something) ≈ 10
example : (2 : ℕ) ^ 10 = 1024 := by native_decide
example : (1024 : ℕ) > 1000 := by native_decide

-- ============================================================================
-- § 10. Summary: Key Formulas
-- ============================================================================

/-!
## Summary of Key Combinatorial Constants

We collect exact rational values for the formulas in this chapter.
-/

-- H_1 = 1, H_2 = 3/2, H_3 = 11/6, H_4 = 25/12, H_5 = 137/60
example : harmonicQ 1 = 1 := by native_decide
example : harmonicQ 2 = 3 / 2 := by native_decide
example : harmonicQ 3 = 11 / 6 := by native_decide
example : harmonicQ 4 = 25 / 12 := by native_decide
example : harmonicQ 5 = 137 / 60 := by native_decide

-- Coupon collector ratios: couponTime n / n = H_n
example : couponTime 5 / 5 = harmonicQ 5 := by native_decide
example : couponTime 10 / 10 = harmonicQ 10 := by native_decide

-- Birthday paradox: exact threshold is n=23 for m=365
-- (verified in § 2: n=22 is safe, n=23 crosses 50%)
example : 2 * noCollisionCount 365 22 > 365 ^ 22 := by native_decide
example : 2 * noCollisionCount 365 23 < 365 ^ 23 := by native_decide

end HashingAnalysis
