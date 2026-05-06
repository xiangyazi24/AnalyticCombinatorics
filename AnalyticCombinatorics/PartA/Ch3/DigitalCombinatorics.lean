import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.DigitalCombinatorics

open Finset Nat


/-! # Digital / Radix-Based Enumeration

Numerical verifications for digital combinatorics topics:
binary representations and bit counts, Gray code, ruler (2-adic valuation) sequence,
Stern–Brocot / Stern's diatomic sequence, de Bruijn sequence counts,
and digit sums base 10. -/

/-! ## 1. Binary Representations and Bit Counts

Among the 2^k binary strings of length k (representing 0 .. 2^k - 1),
the total number of 1-bits equals k · 2^(k-1).
By symmetry, half of the k·2^k bits in all k-bit strings are 1s. -/

/-- Total number of 1-bits across all k-bit binary representations of 0 .. 2^k - 1. -/
def totalBits (k : ℕ) : ℕ := k * 2 ^ (k - 1)

example : totalBits 0 = 0 := by native_decide
example : totalBits 1 = 1 := by native_decide
example : totalBits 2 = 4 := by native_decide
example : totalBits 3 = 12 := by native_decide
example : totalBits 4 = 32 := by native_decide
example : totalBits 5 = 80 := by native_decide

/-- Number of k-bit strings with exactly j ones equals C(k, j). -/
-- 70 eight-bit strings have exactly 4 ones.
example : Nat.choose 8 4 = 70 := by native_decide

-- 252 ten-bit strings have exactly 5 ones.
example : Nat.choose 10 5 = 252 := by native_decide

-- 15 six-bit strings have exactly 2 ones.
example : Nat.choose 6 2 = 15 := by native_decide

-- Sum over j of C(k, j) = 2^k (all k-bit strings).
example : ∑ j ∈ Finset.range 5, Nat.choose 4 j = 2 ^ 4 := by native_decide

/-! ## 2. Gray Code

The standard binary-reflected Gray code maps n ↦ G(n) = n XOR (n >> 1).
Consecutive Gray code words differ in exactly one bit. -/

/-- Standard Gray code: G(n) = n XOR (n / 2). -/
def grayCode (n : ℕ) : ℕ := Nat.xor n (n / 2)

-- Verify the 3-bit Gray code table: 0, 1, 3, 2, 6, 7, 5, 4.
example : grayCode 0 = 0 := by native_decide
example : grayCode 1 = 1 := by native_decide
example : grayCode 2 = 3 := by native_decide
example : grayCode 3 = 2 := by native_decide
example : grayCode 4 = 6 := by native_decide
example : grayCode 5 = 7 := by native_decide
example : grayCode 6 = 5 := by native_decide
example : grayCode 7 = 4 := by native_decide

-- Full 4-bit Gray code table.
def grayTable4 : Fin 16 → ℕ :=
  ![0, 1, 3, 2, 6, 7, 5, 4, 12, 13, 15, 14, 10, 11, 9, 8]

example : ∀ i : Fin 16, grayCode i.val = grayTable4 i := by native_decide

-- grayCode is a bijection on Fin 2^k (values 0 .. 2^k - 1 for k = 4).
example : (Finset.image (fun n : Fin 16 => grayCode n.val) Finset.univ).card = 16 := by
  native_decide

/-! ## 3. Ruler Sequence / 2-Adic Valuation

The ruler sequence records ν₂(n), the 2-adic valuation of n (largest power of 2 dividing n).
When adding 1 to a binary number n, the number of carry operations equals the number
of trailing 1-bits of n, which is ν₂(n + 1).

Key identity: Σ_{i=1}^{2^k} ν₂(i) = 2^k - 1. -/

/-- 2-adic valuation table for i+1, i = 0 .. 15, i.e., ν₂(1) .. ν₂(16).
    ν₂(1)=0, ν₂(2)=1, ν₂(3)=0, ν₂(4)=2, ν₂(5)=0, ν₂(6)=1, ν₂(7)=0, ν₂(8)=3,
    ν₂(9)=0, ν₂(10)=1, ν₂(11)=0, ν₂(12)=2, ν₂(13)=0, ν₂(14)=1, ν₂(15)=0, ν₂(16)=4. -/
def rulerTable : Fin 16 → ℕ := ![0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4]

-- Individual spot checks.
example : rulerTable ⟨0, by norm_num⟩ = 0 := by native_decide   -- ν₂(1) = 0
example : rulerTable ⟨1, by norm_num⟩ = 1 := by native_decide   -- ν₂(2) = 1
example : rulerTable ⟨3, by norm_num⟩ = 2 := by native_decide   -- ν₂(4) = 2
example : rulerTable ⟨7, by norm_num⟩ = 3 := by native_decide   -- ν₂(8) = 3
example : rulerTable ⟨15, by norm_num⟩ = 4 := by native_decide  -- ν₂(16) = 4

-- Σ ν₂(i) for i = 1 .. 2^4 = 2^4 - 1 = 15.
example : ∑ i : Fin 16, rulerTable i = 15 := by native_decide

-- The identity Σ_{i=1}^{2^k} ν₂(i) = 2^k - 1 for k = 3 (values 1 .. 8).
-- ν₂: 0,1,0,2,0,1,0,3 → sum = 7 = 2^3 - 1.
def rulerTable8 : Fin 8 → ℕ := ![0, 1, 0, 2, 0, 1, 0, 3]
example : ∑ i : Fin 8, rulerTable8 i = 7 := by native_decide

/-! ## 4. Stern's Diatomic Sequence

s(0) = 0, s(1) = 1, s(2n) = s(n), s(2n+1) = s(n) + s(n+1).
Every positive rational p/q appears exactly once (in lowest terms) as s(n)/s(n+1). -/

/-- Stern's diatomic sequence s(0) .. s(15). -/
def sternTable : Fin 16 → ℕ := ![0, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3, 5, 2, 5, 3, 4]

-- Spot checks.
example : sternTable ⟨0, by norm_num⟩ = 0 := by native_decide
example : sternTable ⟨1, by norm_num⟩ = 1 := by native_decide
example : sternTable ⟨2, by norm_num⟩ = 1 := by native_decide
example : sternTable ⟨3, by norm_num⟩ = 2 := by native_decide
example : sternTable ⟨4, by norm_num⟩ = 1 := by native_decide
example : sternTable ⟨5, by norm_num⟩ = 3 := by native_decide
example : sternTable ⟨6, by norm_num⟩ = 2 := by native_decide
example : sternTable ⟨7, by norm_num⟩ = 3 := by native_decide
example : sternTable ⟨8, by norm_num⟩ = 1 := by native_decide
example : sternTable ⟨9, by norm_num⟩ = 4 := by native_decide
example : sternTable ⟨15, by norm_num⟩ = 4 := by native_decide

-- Verify recurrence s(2n) = s(n) for indices inside the table.
-- s(2) = s(1) = 1.
example : sternTable ⟨2, by norm_num⟩ = sternTable ⟨1, by norm_num⟩ := by native_decide
-- s(4) = s(2) = 1.
example : sternTable ⟨4, by norm_num⟩ = sternTable ⟨2, by norm_num⟩ := by native_decide
-- s(8) = s(4) = 1.
example : sternTable ⟨8, by norm_num⟩ = sternTable ⟨4, by norm_num⟩ := by native_decide

-- Verify recurrence s(2n+1) = s(n) + s(n+1) for small n.
-- s(3) = s(1) + s(2) = 1 + 1 = 2.
example : sternTable ⟨3, by norm_num⟩ =
    sternTable ⟨1, by norm_num⟩ + sternTable ⟨2, by norm_num⟩ := by native_decide
-- s(5) = s(2) + s(3) = 1 + 2 = 3.
example : sternTable ⟨5, by norm_num⟩ =
    sternTable ⟨2, by norm_num⟩ + sternTable ⟨3, by norm_num⟩ := by native_decide
-- s(7) = s(3) + s(4) = 2 + 1 = 3.
example : sternTable ⟨7, by norm_num⟩ =
    sternTable ⟨3, by norm_num⟩ + sternTable ⟨4, by norm_num⟩ := by native_decide

-- Sum of s(1) .. s(8): known sum identity.
def sternTable8 : Fin 8 → ℕ := ![1, 1, 2, 1, 3, 2, 3, 1]
example : ∑ i : Fin 8, sternTable8 i = 14 := by native_decide

-- gcd(s(n), s(n+1)) = 1 for consecutive terms (coprimality property).
-- Check for consecutive pairs in 0..14.
example : Nat.gcd (sternTable ⟨1, by norm_num⟩) (sternTable ⟨2, by norm_num⟩) = 1 := by
  native_decide
example : Nat.gcd (sternTable ⟨4, by norm_num⟩) (sternTable ⟨5, by norm_num⟩) = 1 := by
  native_decide
example : Nat.gcd (sternTable ⟨9, by norm_num⟩) (sternTable ⟨10, by norm_num⟩) = 1 := by
  native_decide
example : Nat.gcd (sternTable ⟨14, by norm_num⟩) (sternTable ⟨15, by norm_num⟩) = 1 := by
  native_decide

/-! ## 5. de Bruijn Sequences

A binary de Bruijn sequence of order n is a cyclic sequence of length 2^n in which
every binary string of length n appears exactly once as a contiguous substring.

Number of distinct binary de Bruijn sequences of order n = 2^(2^(n-1) - n). -/

/-- Number of binary de Bruijn sequences of order n (n ≥ 1). -/
def deBruijnCount (n : ℕ) : ℕ :=
  if n = 0 then 1 else 2 ^ (2 ^ (n - 1) - n)

example : deBruijnCount 1 = 1 := by native_decide
example : deBruijnCount 2 = 1 := by native_decide   -- 2^(2^1 - 2) = 2^0 = 1
example : deBruijnCount 3 = 2 := by native_decide   -- 2^(2^2 - 3) = 2^1 = 2
example : deBruijnCount 4 = 16 := by native_decide  -- 2^(2^3 - 4) = 2^4 = 16

-- Length of a binary de Bruijn sequence of order n = 2^n.
example : (2 : ℕ) ^ 1 = 2 := by native_decide
example : (2 : ℕ) ^ 2 = 4 := by native_decide
example : (2 : ℕ) ^ 3 = 8 := by native_decide
example : (2 : ℕ) ^ 4 = 16 := by native_decide

-- For order n, the sequence contains exactly 2^n / 2 = 2^(n-1) ones (by balance).
-- E.g. order 3: 4 ones among 8 positions.
example : (2 : ℕ) ^ 3 / 2 = 4 := by native_decide

-- de Bruijn count grows rapidly: order 5 has 2^(2^4 - 5) = 2^11 = 2048.
example : deBruijnCount 5 = 2048 := by native_decide

/-! ## 6. Digit Sums Base 10

The decimal digit sum of n, written S₁₀(n), satisfies:
  S₁₀(n) ≡ n (mod 9)  (casting out nines).
For single-digit n: S₁₀(n) = n.
For n = 10..15: S₁₀(n) = 1,2,3,4,5,6. -/

/-- Decimal digit sums for 0 .. 15. -/
def digitSumBase10 : Fin 16 → ℕ := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6]

-- Spot checks.
example : digitSumBase10 ⟨0, by norm_num⟩ = 0 := by native_decide
example : digitSumBase10 ⟨9, by norm_num⟩ = 9 := by native_decide
example : digitSumBase10 ⟨10, by norm_num⟩ = 1 := by native_decide   -- 1+0
example : digitSumBase10 ⟨11, by norm_num⟩ = 2 := by native_decide   -- 1+1
example : digitSumBase10 ⟨15, by norm_num⟩ = 6 := by native_decide   -- 1+5

-- Sum of digit sums for 0 .. 9 = 0+1+...+9 = 45.
example : ∑ i : Fin 10, digitSumBase10 ⟨i.val, by omega⟩ = 45 := by native_decide

-- Congruence: n ≡ S₁₀(n) (mod 9) for n in 0..15.
example : ∀ i : Fin 16, i.val % 9 = digitSumBase10 i % 9 := by native_decide

-- Sum of digit sums for 10 .. 15 = 1+2+3+4+5+6 = 21.
example : ∑ i : Fin 6, digitSumBase10 ⟨10 + i.val, by omega⟩ = 21 := by native_decide

-- Maximum digit sum for a 2-digit number (0..99) is 18 (for n=99).
-- Minimum nonzero digit sum for a 2-digit number is 1 (for n=10).
example : digitSumBase10 ⟨10, by norm_num⟩ = 1 := by native_decide

-- Arithmetic: digit sum of 99 via the casting-out-nines formula.
-- 99 mod 9 = 0, so S₁₀(99) ≡ 0 (mod 9); and S₁₀(99) = 18.
example : 99 % 9 = 0 := by native_decide
example : 18 % 9 = 0 := by native_decide

/-! ## 7. Additional Binary Combinatorics

Auxiliary results connecting binary representations to counting. -/

-- Number of even numbers in 0 .. 2^k - 1 equals 2^(k-1).
example : (Finset.filter (fun n => n % 2 = 0) (Finset.range 16)).card = 8 := by native_decide

-- Number of multiples of 4 in 0 .. 2^k - 1 for k = 4.
example : (Finset.filter (fun n => n % 4 = 0) (Finset.range 16)).card = 4 := by native_decide

-- Hamming weight (number of 1-bits) via direct testBit checks.
-- 0 = 0b0000: no bits set.
example : ¬ Nat.testBit 0 0 := by native_decide
-- 7 = 0b111: bits 0,1,2 are set.
example : Nat.testBit 7 0 = true := by native_decide
example : Nat.testBit 7 1 = true := by native_decide
example : Nat.testBit 7 2 = true := by native_decide
example : Nat.testBit 7 3 = false := by native_decide
-- 15 = 0b1111: bits 0,1,2,3 are set; bit 4 is clear.
example : Nat.testBit 15 0 = true := by native_decide
example : Nat.testBit 15 3 = true := by native_decide
example : Nat.testBit 15 4 = false := by native_decide

-- Count of 1-bits in n = Σ_{i} (n >>> i) % 2 (each term is 0 or 1).
-- For 7 = 111₂: sum over 4 bit positions = 3.
example : (∑ i ∈ Finset.range 4, Nat.shiftRight 7 i % 2) = 3 := by native_decide
-- For 255 = 11111111₂: 8 ones over 9 bit positions.
example : (∑ i ∈ Finset.range 9, Nat.shiftRight 255 i % 2) = 8 := by native_decide

-- Sum of 1-bit counts for 0 .. 2^k - 1 = k · 2^(k-1) = totalBits k.
-- For k=3: Σ_{n<8} bitcount(n) = 12 = totalBits 3.
example : (∑ n ∈ Finset.range 8,
    ∑ i ∈ Finset.range 4, Nat.shiftRight n i % 2) = totalBits 3 := by native_decide
-- For k=4: Σ_{n<16} bitcount(n) = 32 = totalBits 4.
example : (∑ n ∈ Finset.range 16,
    ∑ i ∈ Finset.range 5, Nat.shiftRight n i % 2) = totalBits 4 := by native_decide

-- Binary palindromes in 0 .. 15: numbers whose binary representation reads the same
-- forwards and backwards. Single bits are trivially palindromic.
-- 4-bit palindromes: 0000=0, 0110=6, 1001=9, 1111=15 (and length < 4: 0,1,2,3,4,5...).
-- Among 4-bit numbers (8..15): 1001=9, 1111=15.
example : Nat.testBit 9 0 = true  := by native_decide
example : Nat.testBit 9 3 = true  := by native_decide
example : Nat.testBit 9 1 = false := by native_decide
example : Nat.testBit 9 2 = false := by native_decide

-- Bitwise operations: XOR, AND, OR for spot checks.
example : Nat.xor 5 3 = 6 := by native_decide   -- 101 XOR 011 = 110
example : Nat.land 5 3 = 1 := by native_decide   -- 101 AND 011 = 001
example : Nat.lor 5 3 = 7 := by native_decide    -- 101 OR  011 = 111

/-- Total bit-count sample for five-bit words. -/
theorem totalBits_five :
    totalBits 5 = 80 := by
  native_decide

/-- Gray-code table sample at the last four-bit word. -/
theorem grayTable4_last :
    grayTable4 15 = 8 := by
  native_decide

/-- De Bruijn sequence count sample at order five. -/
theorem deBruijnCount_five :
    deBruijnCount 5 = 2048 := by
  native_decide

/-- Decimal digit-sum table sample. -/
theorem digitSumBase10_fifteen :
    digitSumBase10 15 = 6 := by
  native_decide



structure DigitalCombinatoricsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DigitalCombinatoricsBudgetCertificate.controlled
    (c : DigitalCombinatoricsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DigitalCombinatoricsBudgetCertificate.budgetControlled
    (c : DigitalCombinatoricsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DigitalCombinatoricsBudgetCertificate.Ready
    (c : DigitalCombinatoricsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DigitalCombinatoricsBudgetCertificate.size
    (c : DigitalCombinatoricsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem digitalCombinatorics_budgetCertificate_le_size
    (c : DigitalCombinatoricsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDigitalCombinatoricsBudgetCertificate :
    DigitalCombinatoricsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleDigitalCombinatoricsBudgetCertificate.Ready := by
  constructor
  · norm_num [DigitalCombinatoricsBudgetCertificate.controlled,
      sampleDigitalCombinatoricsBudgetCertificate]
  · norm_num [DigitalCombinatoricsBudgetCertificate.budgetControlled,
      sampleDigitalCombinatoricsBudgetCertificate]

example :
    sampleDigitalCombinatoricsBudgetCertificate.certificateBudgetWindow ≤
      sampleDigitalCombinatoricsBudgetCertificate.size := by
  apply digitalCombinatorics_budgetCertificate_le_size
  constructor
  · norm_num [DigitalCombinatoricsBudgetCertificate.controlled,
      sampleDigitalCombinatoricsBudgetCertificate]
  · norm_num [DigitalCombinatoricsBudgetCertificate.budgetControlled,
      sampleDigitalCombinatoricsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDigitalCombinatoricsBudgetCertificate.Ready := by
  constructor
  · norm_num [DigitalCombinatoricsBudgetCertificate.controlled,
      sampleDigitalCombinatoricsBudgetCertificate]
  · norm_num [DigitalCombinatoricsBudgetCertificate.budgetControlled,
      sampleDigitalCombinatoricsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDigitalCombinatoricsBudgetCertificate.certificateBudgetWindow ≤
      sampleDigitalCombinatoricsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DigitalCombinatoricsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDigitalCombinatoricsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDigitalCombinatoricsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.DigitalCombinatorics
