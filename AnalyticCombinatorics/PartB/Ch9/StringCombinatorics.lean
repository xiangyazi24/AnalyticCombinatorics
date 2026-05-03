import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace StringCombinatorics

/-!
# String combinatorics and pattern matching probabilities

Finite computational checks for binary strings, pattern avoidance, overlap
autocorrelation, waiting times, Conway leading numbers, and Lyndon word counts.
These are small exact tables in the spirit of Chapter IX of Analytic
Combinatorics.
-/

section BinaryStrings

/-- Number of binary strings of length `n`. -/
def binaryStringCount (n : ℕ) : ℕ :=
  2 ^ n

def binaryStringCountTable : Fin 13 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]

theorem binary_string_counts_n0_to_n12 :
    binaryStringCountTable 0 = binaryStringCount 0 ∧
    binaryStringCountTable 1 = binaryStringCount 1 ∧
    binaryStringCountTable 2 = binaryStringCount 2 ∧
    binaryStringCountTable 3 = binaryStringCount 3 ∧
    binaryStringCountTable 4 = binaryStringCount 4 ∧
    binaryStringCountTable 5 = binaryStringCount 5 ∧
    binaryStringCountTable 6 = binaryStringCount 6 ∧
    binaryStringCountTable 7 = binaryStringCount 7 ∧
    binaryStringCountTable 8 = binaryStringCount 8 ∧
    binaryStringCountTable 9 = binaryStringCount 9 ∧
    binaryStringCountTable 10 = binaryStringCount 10 ∧
    binaryStringCountTable 11 = binaryStringCount 11 ∧
    binaryStringCountTable 12 = binaryStringCount 12 := by native_decide

end BinaryStrings

section PatternAvoidance

/-- Fibonacci numbers with `fib 0 = 0`, `fib 1 = 1`. -/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- The `i`th bit of the length-`n` binary word encoded by `x`, read left to right. -/
def bitAt (n i x : ℕ) : Bool :=
  x / 2 ^ (n - 1 - i) % 2 = 1

/-- The length-`n` binary word encoded by `x`, as a Boolean list. -/
def binaryWord (n x : ℕ) : List Bool :=
  (List.range n).map (fun i => bitAt n i x)

/-- Boolean pattern occurrence at position `i`. -/
def occursAt (w p : List Bool) (i : ℕ) : Bool :=
  decide (i + p.length ≤ w.length) &&
    (List.range p.length).all (fun j => w.getD (i + j) false == p.getD j false)

/-- Whether a word contains a Boolean pattern. -/
def containsPattern (w p : List Bool) : Bool :=
  (List.range (w.length + 1)).any (fun i => occursAt w p i)

/-- Whether the length-`n` binary word encoded by `x` avoids pattern `p`. -/
def avoidsPattern (p : List Bool) (n x : ℕ) : Bool :=
  !containsPattern (binaryWord n x) p

/-- Number of length-`n` binary words avoiding pattern `p`. -/
def countAvoiding (p : List Bool) (n : ℕ) : ℕ :=
  ((Finset.range (2 ^ n)).filter (fun x => avoidsPattern p n x = true)).card

def pattern11 : List Bool := [true, true]
def pattern00 : List Bool := [false, false]
def pattern010 : List Bool := [false, true, false]

def noConsecutiveOnesCount (n : ℕ) : ℕ :=
  countAvoiding pattern11 n

def noConsecutiveZerosCount (n : ℕ) : ℕ :=
  countAvoiding pattern00 n

def avoiding010Count (n : ℕ) : ℕ :=
  countAvoiding pattern010 n

def noConsecutiveOnesTable : Fin 11 → ℕ :=
  ![1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144]

def noConsecutiveZerosTable : Fin 11 → ℕ :=
  ![1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144]

def avoiding010Table : Fin 9 → ℕ :=
  ![1, 2, 4, 7, 12, 21, 37, 65, 114]

theorem fibonacci_values_f2_to_f12 :
    fib 2 = 1 ∧
    fib 3 = 2 ∧
    fib 4 = 3 ∧
    fib 5 = 5 ∧
    fib 6 = 8 ∧
    fib 7 = 13 ∧
    fib 8 = 21 ∧
    fib 9 = 34 ∧
    fib 10 = 55 ∧
    fib 11 = 89 ∧
    fib 12 = 144 := by native_decide

theorem avoiding_11_fibonacci_n0_to_n10 :
    noConsecutiveOnesCount 0 = fib (0 + 2) ∧
    noConsecutiveOnesCount 1 = fib (1 + 2) ∧
    noConsecutiveOnesCount 2 = fib (2 + 2) ∧
    noConsecutiveOnesCount 3 = fib (3 + 2) ∧
    noConsecutiveOnesCount 4 = fib (4 + 2) ∧
    noConsecutiveOnesCount 5 = fib (5 + 2) ∧
    noConsecutiveOnesCount 6 = fib (6 + 2) ∧
    noConsecutiveOnesCount 7 = fib (7 + 2) ∧
    noConsecutiveOnesCount 8 = fib (8 + 2) ∧
    noConsecutiveOnesCount 9 = fib (9 + 2) ∧
    noConsecutiveOnesCount 10 = fib (10 + 2) := by native_decide

theorem avoiding_11_table_checks :
    noConsecutiveOnesTable 0 = noConsecutiveOnesCount 0 ∧
    noConsecutiveOnesTable 1 = noConsecutiveOnesCount 1 ∧
    noConsecutiveOnesTable 2 = noConsecutiveOnesCount 2 ∧
    noConsecutiveOnesTable 3 = noConsecutiveOnesCount 3 ∧
    noConsecutiveOnesTable 4 = noConsecutiveOnesCount 4 ∧
    noConsecutiveOnesTable 5 = noConsecutiveOnesCount 5 ∧
    noConsecutiveOnesTable 6 = noConsecutiveOnesCount 6 ∧
    noConsecutiveOnesTable 7 = noConsecutiveOnesCount 7 ∧
    noConsecutiveOnesTable 8 = noConsecutiveOnesCount 8 ∧
    noConsecutiveOnesTable 9 = noConsecutiveOnesCount 9 ∧
    noConsecutiveOnesTable 10 = noConsecutiveOnesCount 10 := by native_decide

theorem avoiding_00_fibonacci_n0_to_n10 :
    noConsecutiveZerosCount 0 = fib (0 + 2) ∧
    noConsecutiveZerosCount 1 = fib (1 + 2) ∧
    noConsecutiveZerosCount 2 = fib (2 + 2) ∧
    noConsecutiveZerosCount 3 = fib (3 + 2) ∧
    noConsecutiveZerosCount 4 = fib (4 + 2) ∧
    noConsecutiveZerosCount 5 = fib (5 + 2) ∧
    noConsecutiveZerosCount 6 = fib (6 + 2) ∧
    noConsecutiveZerosCount 7 = fib (7 + 2) ∧
    noConsecutiveZerosCount 8 = fib (8 + 2) ∧
    noConsecutiveZerosCount 9 = fib (9 + 2) ∧
    noConsecutiveZerosCount 10 = fib (10 + 2) := by native_decide

theorem avoiding_00_same_count_as_avoiding_11 :
    noConsecutiveZerosCount 0 = noConsecutiveOnesCount 0 ∧
    noConsecutiveZerosCount 1 = noConsecutiveOnesCount 1 ∧
    noConsecutiveZerosCount 2 = noConsecutiveOnesCount 2 ∧
    noConsecutiveZerosCount 3 = noConsecutiveOnesCount 3 ∧
    noConsecutiveZerosCount 4 = noConsecutiveOnesCount 4 ∧
    noConsecutiveZerosCount 5 = noConsecutiveOnesCount 5 ∧
    noConsecutiveZerosCount 6 = noConsecutiveOnesCount 6 ∧
    noConsecutiveZerosCount 7 = noConsecutiveOnesCount 7 ∧
    noConsecutiveZerosCount 8 = noConsecutiveOnesCount 8 ∧
    noConsecutiveZerosCount 9 = noConsecutiveOnesCount 9 ∧
    noConsecutiveZerosCount 10 = noConsecutiveOnesCount 10 := by native_decide

theorem avoiding_00_table_checks :
    noConsecutiveZerosTable 0 = noConsecutiveZerosCount 0 ∧
    noConsecutiveZerosTable 1 = noConsecutiveZerosCount 1 ∧
    noConsecutiveZerosTable 2 = noConsecutiveZerosCount 2 ∧
    noConsecutiveZerosTable 3 = noConsecutiveZerosCount 3 ∧
    noConsecutiveZerosTable 4 = noConsecutiveZerosCount 4 ∧
    noConsecutiveZerosTable 5 = noConsecutiveZerosCount 5 ∧
    noConsecutiveZerosTable 6 = noConsecutiveZerosCount 6 ∧
    noConsecutiveZerosTable 7 = noConsecutiveZerosCount 7 ∧
    noConsecutiveZerosTable 8 = noConsecutiveZerosCount 8 ∧
    noConsecutiveZerosTable 9 = noConsecutiveZerosCount 9 ∧
    noConsecutiveZerosTable 10 = noConsecutiveZerosCount 10 := by native_decide

theorem avoiding_010_values_n0_to_n8 :
    avoiding010Table 0 = avoiding010Count 0 ∧
    avoiding010Table 1 = avoiding010Count 1 ∧
    avoiding010Table 2 = avoiding010Count 2 ∧
    avoiding010Table 3 = avoiding010Count 3 ∧
    avoiding010Table 4 = avoiding010Count 4 ∧
    avoiding010Table 5 = avoiding010Count 5 ∧
    avoiding010Table 6 = avoiding010Count 6 ∧
    avoiding010Table 7 = avoiding010Count 7 ∧
    avoiding010Table 8 = avoiding010Count 8 := by native_decide

theorem avoiding_010_differs_from_fibonacci :
    avoiding010Count 3 ≠ fib (3 + 2) ∧
    avoiding010Count 4 ≠ fib (4 + 2) ∧
    avoiding010Count 8 ≠ fib (8 + 2) := by native_decide

end PatternAvoidance

section OverlapsAndWaitingTimes

def H : Bool := true
def T : Bool := false

def patternHH : List Bool := [H, H]
def patternHT : List Bool := [H, T]
def patternTH : List Bool := [T, H]
def patternTT : List Bool := [T, T]
def patternHHH : List Bool := [H, H, H]
def patternHHT : List Bool := [H, H, T]
def patternHTH : List Bool := [H, T, H]

/--
Autocorrelation at shift `s`: the suffix of length `p.length - s` agrees with
the prefix of that length. This overlap capacity affects waiting times.
-/
def overlapAtShift (p : List Bool) (s : ℕ) : Bool :=
  decide (s < p.length) &&
    (List.range (p.length - s)).all (fun i => p.getD i false == p.getD (i + s) false)

/-- Autocorrelation polynomial coefficients, indexed by shifts. -/
def autocorrelationPolynomial (p : List Bool) : Fin p.length → ℕ :=
  fun s => if overlapAtShift p s.val then 1 else 0

/-- The same autocorrelation coefficient, with a plain natural-number shift. -/
def autocorrelationCoefficient (p : List Bool) (s : ℕ) : ℕ :=
  if overlapAtShift p s then 1 else 0

def autocorrelationHH : Fin 2 → ℕ := ![1, 1]
def autocorrelationHT : Fin 2 → ℕ := ![1, 0]
def autocorrelationHHT : Fin 3 → ℕ := ![1, 0, 0]
def autocorrelationHTH : Fin 3 → ℕ := ![1, 0, 1]

/-- Expected wait for a pattern over an equiprobable alphabet of size `alphabetSize`. -/
def expectedWaitUniform (alphabetSize : ℕ) (p : List Bool) : ℕ :=
  (Finset.range p.length).sum
    (fun s => if overlapAtShift p s then alphabetSize ^ (p.length - s) else 0)

/-- Prefix-suffix agreement of a fixed positive overlap length. -/
def prefixSuffixOverlapLength (p : List Bool) (len : ℕ) : Bool :=
  decide (0 < len ∧ len ≤ p.length) &&
    (List.range len).all
      (fun i => p.getD i false == p.getD (p.length - len + i) false)

/--
Conway leading number for a coin pattern: overlap bits weighted by powers of two.
For a fair coin, the expected wait is twice this number.
-/
def conwayLeadingNumber (p : List Bool) : ℕ :=
  (Finset.range p.length).sum
    (fun r => if prefixSuffixOverlapLength p (r + 1) then 2 ^ r else 0)

theorem autocorrelation_polynomial_short_patterns :
    autocorrelationHH 0 = autocorrelationCoefficient patternHH 0 ∧
    autocorrelationHH 1 = autocorrelationCoefficient patternHH 1 ∧
    autocorrelationHT 0 = autocorrelationCoefficient patternHT 0 ∧
    autocorrelationHT 1 = autocorrelationCoefficient patternHT 1 ∧
    autocorrelationHHT 0 = autocorrelationCoefficient patternHHT 0 ∧
    autocorrelationHHT 1 = autocorrelationCoefficient patternHHT 1 ∧
    autocorrelationHHT 2 = autocorrelationCoefficient patternHHT 2 ∧
    autocorrelationHTH 0 = autocorrelationCoefficient patternHTH 0 ∧
    autocorrelationHTH 1 = autocorrelationCoefficient patternHTH 1 ∧
    autocorrelationHTH 2 = autocorrelationCoefficient patternHTH 2 := by native_decide

theorem expected_wait_HH_partial_computation :
    expectedWaitUniform 2 patternHH = 2 ^ 2 + 2 ^ 1 ∧
    expectedWaitUniform 2 patternHH = 6 := by native_decide

theorem expected_wait_HT :
    expectedWaitUniform 2 patternHT = 2 ^ 2 ∧
    expectedWaitUniform 2 patternHT = 4 := by native_decide

theorem conway_leading_number_short_patterns :
    conwayLeadingNumber patternHH = 3 ∧
    conwayLeadingNumber patternHT = 2 ∧
    conwayLeadingNumber patternTH = 2 ∧
    conwayLeadingNumber patternTT = 3 ∧
    conwayLeadingNumber patternHHH = 7 ∧
    conwayLeadingNumber patternHHT = 4 ∧
    conwayLeadingNumber patternHTH = 5 := by native_decide

theorem expected_wait_equals_twice_conway_for_short_patterns :
    expectedWaitUniform 2 patternHH = 2 * conwayLeadingNumber patternHH ∧
    expectedWaitUniform 2 patternHT = 2 * conwayLeadingNumber patternHT ∧
    expectedWaitUniform 2 patternTT = 2 * conwayLeadingNumber patternTT ∧
    expectedWaitUniform 2 patternHHH = 2 * conwayLeadingNumber patternHHH ∧
    expectedWaitUniform 2 patternHHT = 2 * conwayLeadingNumber patternHHT ∧
    expectedWaitUniform 2 patternHTH = 2 * conwayLeadingNumber patternHTH := by native_decide

end OverlapsAndWaitingTimes

section LyndonWords

/-- Small Möbius values sufficient for the finite Lyndon table below. -/
def mobiusSmall : ℕ → ℤ
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => 0
  | 5 => -1
  | 6 => 1
  | 7 => -1
  | 8 => 0
  | _ => 0

def divisors (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun d => d ≠ 0 ∧ n % d = 0)

/-- Numerator in the Lyndon formula: `Σ_{d|n} μ(n/d) k^d`. -/
def lyndonNumerator (k n : ℕ) : ℤ :=
  ∑ d ∈ divisors n, mobiusSmall (n / d) * (k : ℤ) ^ d

/-- Lyndon words of length `n` over a `k`-letter alphabet. -/
def lyndonFormula (k n : ℕ) : ℤ :=
  lyndonNumerator k n / (n : ℤ)

def binaryLyndonTable : Fin 8 → ℤ :=
  ![2, 1, 2, 3, 6, 9, 18, 30]

theorem lyndon_formula_binary_values_n1_to_n8 :
    lyndonFormula 2 1 = 2 ∧
    lyndonFormula 2 2 = 1 ∧
    lyndonFormula 2 3 = 2 ∧
    lyndonFormula 2 4 = 3 ∧
    lyndonFormula 2 5 = 6 ∧
    lyndonFormula 2 6 = 9 ∧
    lyndonFormula 2 7 = 18 ∧
    lyndonFormula 2 8 = 30 := by native_decide

theorem binary_lyndon_table_checks :
    binaryLyndonTable 0 = lyndonFormula 2 1 ∧
    binaryLyndonTable 1 = lyndonFormula 2 2 ∧
    binaryLyndonTable 2 = lyndonFormula 2 3 ∧
    binaryLyndonTable 3 = lyndonFormula 2 4 ∧
    binaryLyndonTable 4 = lyndonFormula 2 5 ∧
    binaryLyndonTable 5 = lyndonFormula 2 6 ∧
    binaryLyndonTable 6 = lyndonFormula 2 7 ∧
    binaryLyndonTable 7 = lyndonFormula 2 8 := by native_decide

end LyndonWords

end StringCombinatorics
