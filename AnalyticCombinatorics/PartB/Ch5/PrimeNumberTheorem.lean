import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace PrimeNumberTheorem

/-! # Prime Number Theorem and Analytic Combinatorics Connections
  Flajolet & Sedgewick, Part B, Chapter 5: prime counting via Dirichlet
  series, Chebyshev bounds, and the distribution of primes. -/

/-! ## Computable Primality and Prime Counting -/

def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else (List.range (n - 2)).all fun i => n % (i + 2) != 0

def primePi (n : Nat) : Nat :=
  ((List.range (n + 1)).filter fun k => isPrime k).length

def primesUpTo (n : Nat) : List Nat :=
  (List.range (n + 1)).filter fun k => isPrime k

example : primePi 10 = 4 := by native_decide
example : primePi 20 = 8 := by native_decide
example : primePi 30 = 10 := by native_decide
example : primePi 100 = 25 := by native_decide

example : primesUpTo 10 = [2, 3, 5, 7] := by native_decide
example : primesUpTo 30 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29] := by native_decide
example : primePi 2 = 1 := by native_decide
example : primePi 50 = 15 := by native_decide

/-! ## Chebyshev Bounds via Primorial -/

def primorial (n : Nat) : Nat :=
  (primesUpTo n).foldl (· * ·) 1

example : primorial 10 = 210 := by native_decide
example : primorial 20 = 9699690 := by native_decide
example : primorial 30 = 6469693230 := by native_decide

theorem chebyshev_lower_10 : 2 ^ 5 ≤ primorial 10 := by native_decide
theorem chebyshev_lower_20 : 2 ^ 10 ≤ primorial 20 := by native_decide
theorem chebyshev_lower_30 : 2 ^ 15 ≤ primorial 30 := by native_decide

theorem chebyshev_upper_10 : primorial 10 ≤ 4 ^ 10 := by native_decide
theorem chebyshev_upper_20 : primorial 20 ≤ 4 ^ 20 := by native_decide
theorem chebyshev_upper_30 : primorial 30 ≤ 4 ^ 30 := by native_decide

theorem pi_bounds_100 : 10 < primePi 100 ∧ primePi 100 < 50 := by native_decide

/-! ## Prime Powers and Von Mangoldt Function -/

def smallestPrimeFactor (n : Nat) : Nat :=
  if n < 2 then 0
  else match (List.range (n - 1)).find? fun i => n % (i + 2) == 0 with
    | some i => i + 2
    | none => n

def isPrimePower (n : Nat) : Bool :=
  if n < 2 then false
  else (List.range n).any fun k => (smallestPrimeFactor n) ^ (k + 1) == n

def primeBase (n : Nat) : Nat :=
  if isPrimePower n then smallestPrimeFactor n else 0

example : isPrimePower 8 = true := by native_decide
example : isPrimePower 27 = true := by native_decide
example : isPrimePower 6 = false := by native_decide
example : primeBase 32 = 2 := by native_decide
example : primeBase 49 = 7 := by native_decide

def primePowerCount (n : Nat) : Nat :=
  ((List.range (n + 1)).filter fun k => isPrimePower k).length

example : primePowerCount 30 = 16 := by native_decide

/-! ## Euler Totient and Möbius Function -/

def eulerTotient (n : Nat) : Nat :=
  if n == 0 then 0
  else ((List.range n).filter fun k => Nat.gcd (k + 1) n == 1).length

example : eulerTotient 1 = 1 := by native_decide
example : eulerTotient 10 = 4 := by native_decide
example : eulerTotient 12 = 4 := by native_decide
example : eulerTotient 30 = 8 := by native_decide

def totientDivisorSum (n : Nat) : Nat :=
  ((List.range n).filter fun d => n % (d + 1) == 0).foldl
    (fun acc d => acc + eulerTotient (d + 1)) 0

theorem totient_sum_12 : totientDivisorSum 12 = 12 := by native_decide
theorem totient_sum_30 : totientDivisorSum 30 = 30 := by native_decide

def isSquareFree (n : Nat) : Bool :=
  if n < 1 then false
  else (List.range (n - 1)).all fun i => n % ((i + 2) * (i + 2)) != 0

def primeFactorCount (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else ((List.range (n - 1)).filter fun i =>
    isPrime (i + 2) && n % (i + 2) == 0).length

def moebius (n : Nat) : Int :=
  if n == 0 || !isSquareFree n then 0
  else if primeFactorCount n % 2 == 0 then 1 else -1

example : moebius 1 = 1 := by native_decide
example : moebius 2 = -1 := by native_decide
example : moebius 6 = 1 := by native_decide
example : moebius 4 = 0 := by native_decide

def moebiusDivisorSum (n : Nat) : Int :=
  ((List.range n).filter fun d => n % (d + 1) == 0).foldl
    (fun acc d => acc + moebius (d + 1)) 0

theorem moebius_sum_1 : moebiusDivisorSum 1 = 1 := by native_decide
theorem moebius_sum_12 : moebiusDivisorSum 12 = 0 := by native_decide
theorem moebius_sum_30 : moebiusDivisorSum 30 = 0 := by native_decide

/-! ## Dirichlet Series and Euler Products -/

def reciprocalPrimeSum (n : Nat) : ℚ :=
  (primesUpTo n).foldl (fun acc p => acc + 1 / (p : ℚ)) 0

example : reciprocalPrimeSum 10 = 247 / 210 := by native_decide

def eulerProductS1 (n : Nat) : ℚ :=
  (primesUpTo n).foldl (fun acc p =>
    acc * (p : ℚ) / ((p : ℚ) - 1)) 1

example : eulerProductS1 10 = 35 / 8 := by native_decide

def eulerProductS2 (n : Nat) : ℚ :=
  (primesUpTo n).foldl (fun acc p =>
    acc * ((p : ℚ) ^ 2) / ((p : ℚ) ^ 2 - 1)) 1

example : eulerProductS2 10 = 1225 / 768 := by native_decide

/-! ## Bertrand's Postulate (Computational Verification) -/

def hasPrimeInRange (lo hi : Nat) : Bool :=
  (List.range (hi - lo)).any fun i => isPrime (lo + 1 + i)

def bertrandCheck (n : Nat) : Bool :=
  n == 0 || hasPrimeInRange n (2 * n)

def bertrandHoldsUpTo (N : Nat) : Bool :=
  (List.range N).all fun i => bertrandCheck (i + 1)

theorem bertrand_verified_50 : bertrandHoldsUpTo 50 = true := by native_decide

/-! ## PNT Ratio Approximation -/

def pntRatioScaled (n : Nat) : Nat :=
  if n == 0 then 0 else primePi n * 10000 / n

theorem pnt_ratio_decreasing :
    pntRatioScaled 100 < pntRatioScaled 10 := by native_decide

theorem pi_sublinear :
    ∀ n : Fin 101, (n : Nat) ≤ 1 ∨ primePi n < n := by native_decide

/-! ## Abstract Theorems -/

theorem infinitely_many_primes :
    ∀ n : ℕ, ∃ p : ℕ, p > n ∧ isPrime p = true := sorry

theorem dirichlet_arithmetic_progression :
    ∀ a d : ℕ, d > 0 → Nat.gcd a d = 1 →
      ∀ N : ℕ, ∃ k : ℕ, k > N ∧ isPrime (a + k * d) = true := sorry

end PrimeNumberTheorem
