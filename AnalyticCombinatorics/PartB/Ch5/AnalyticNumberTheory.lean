import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticNumberTheory

def primeCountingAtEven : Fin 15 → ℕ :=
  ![1, 2, 3, 4, 4, 5, 6, 6, 7, 8, 8, 9, 9, 9, 10]

def primesUpToThirty : Fin 10 → ℕ :=
  ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

def primeGapsUpToThirty : Fin 9 → ℕ :=
  ![1, 2, 2, 4, 2, 4, 2, 4, 6]

def smallPrime : ℕ → Bool
  | 2 => true
  | 3 => true
  | 5 => true
  | 7 => true
  | 11 => true
  | 13 => true
  | 17 => true
  | 19 => true
  | 23 => true
  | 29 => true
  | 31 => true
  | 37 => true
  | 41 => true
  | 43 => true
  | 47 => true
  | 53 => true
  | 59 => true
  | 61 => true
  | 67 => true
  | 71 => true
  | 73 => true
  | 79 => true
  | 83 => true
  | 89 => true
  | 97 => true
  | _ => false

def goldbachEvenLower : Fin 14 → ℕ :=
  ![4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30]

def goldbachLowerLeft : Fin 14 → ℕ :=
  ![2, 3, 3, 3, 5, 3, 3, 5, 3, 3, 5, 3, 5, 7]

def goldbachLowerRight : Fin 14 → ℕ :=
  ![2, 3, 5, 7, 7, 11, 13, 13, 17, 19, 19, 23, 23, 23]

def goldbachEvenUpper : Fin 10 → ℕ :=
  ![32, 34, 36, 38, 40, 42, 44, 46, 48, 50]

def goldbachUpperLeft : Fin 10 → ℕ :=
  ![3, 3, 5, 7, 3, 5, 3, 3, 5, 3]

def goldbachUpperRight : Fin 10 → ℕ :=
  ![29, 31, 31, 31, 37, 37, 41, 43, 43, 47]

def twinPrimeFirst : Fin 8 → ℕ :=
  ![3, 5, 11, 17, 29, 41, 59, 71]

def twinPrimeSecond : Fin 8 → ℕ :=
  ![5, 7, 13, 19, 31, 43, 61, 73]

def legendreSieveN : Fin 10 → ℕ :=
  ![10, 10, 10, 10, 20, 20, 20, 30, 30, 30]

def legendreSieveA : Fin 10 → ℕ :=
  ![0, 1, 2, 3, 1, 2, 3, 1, 2, 3]

def legendreSievePhi : Fin 10 → ℕ :=
  ![10, 5, 3, 2, 10, 7, 6, 15, 10, 8]

def mobiusLower : Fin 10 → Int :=
  ![1, -1, -1, 0, -1, 1, -1, 0, 0, 1]

def mertensLower : Fin 10 → Int :=
  ![1, 0, -1, -1, -2, -1, -2, -2, -2, -1]

def mobiusUpper : Fin 10 → Int :=
  ![-1, 0, -1, 1, 1, 0, -1, 0, -1, 0]

def mertensUpper : Fin 10 → Int :=
  ![-2, -2, -3, -2, -1, -1, -2, -2, -3, -3]

theorem prime_counting_even_samples :
    primeCountingAtEven 0 = 1 ∧
      primeCountingAtEven 4 = 4 ∧
      primeCountingAtEven 9 = 8 ∧
      primeCountingAtEven 14 = 10 := by
  native_decide

theorem prime_gap_samples :
    primeGapsUpToThirty 0 = primesUpToThirty 1 - primesUpToThirty 0 ∧
      primeGapsUpToThirty 3 = primesUpToThirty 4 - primesUpToThirty 3 ∧
      primeGapsUpToThirty 8 = primesUpToThirty 9 - primesUpToThirty 8 := by
  native_decide

theorem goldbach_lower_verified :
    ∀ i : Fin 14,
      smallPrime (goldbachLowerLeft i) = true ∧
        smallPrime (goldbachLowerRight i) = true ∧
          goldbachLowerLeft i + goldbachLowerRight i = goldbachEvenLower i := by
  native_decide

theorem goldbach_upper_verified :
    ∀ i : Fin 10,
      smallPrime (goldbachUpperLeft i) = true ∧
        smallPrime (goldbachUpperRight i) = true ∧
          goldbachUpperLeft i + goldbachUpperRight i = goldbachEvenUpper i := by
  native_decide

theorem twin_prime_pairs_verified :
    ∀ i : Fin 8,
      smallPrime (twinPrimeFirst i) = true ∧
        smallPrime (twinPrimeSecond i) = true ∧
          twinPrimeFirst i + 2 = twinPrimeSecond i := by
  native_decide

theorem legendre_sieve_small_cases :
    legendreSievePhi 0 = legendreSieveN 0 ∧
      legendreSievePhi 1 = 5 ∧
      legendreSievePhi 3 = 2 ∧
      legendreSievePhi 6 = 6 ∧
      legendreSievePhi 9 = 8 := by
  native_decide

theorem mertens_lower_values :
    mertensLower 0 = mobiusLower 0 ∧
      mertensLower 4 = -2 ∧
      mertensLower 9 = -1 := by
  native_decide

theorem mertens_upper_values :
    mertensUpper 0 = mertensLower 9 + mobiusUpper 0 ∧
      mertensUpper 4 = -1 ∧
      mertensUpper 9 = -3 := by
  native_decide

end AnalyticNumberTheory
