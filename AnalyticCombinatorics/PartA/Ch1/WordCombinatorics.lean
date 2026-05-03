import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace WordCombinatorics

/-!
  Finite word-counting tables from Chapter I style symbolic combinatorics.

  The entries are deliberately small and concrete: each table is indexed by
  `Fin n`, and each check is a closed proposition discharged by native
  computation.
-/

/-! ## Binary words avoiding `11` -/

/-- Binary words of length `n`, for `0 ≤ n ≤ 11`, avoiding the factor `11`. -/
def binaryWordsAvoidingEleven : Fin 12 → ℕ :=
  ![1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233]

/-- Fibonacci-type recurrence for the first bounded values. -/
theorem binaryWordsAvoidingEleven_recurrence :
    binaryWordsAvoidingEleven 2 = binaryWordsAvoidingEleven 1 + binaryWordsAvoidingEleven 0 ∧
    binaryWordsAvoidingEleven 3 = binaryWordsAvoidingEleven 2 + binaryWordsAvoidingEleven 1 ∧
    binaryWordsAvoidingEleven 4 = binaryWordsAvoidingEleven 3 + binaryWordsAvoidingEleven 2 ∧
    binaryWordsAvoidingEleven 5 = binaryWordsAvoidingEleven 4 + binaryWordsAvoidingEleven 3 ∧
    binaryWordsAvoidingEleven 6 = binaryWordsAvoidingEleven 5 + binaryWordsAvoidingEleven 4 ∧
    binaryWordsAvoidingEleven 7 = binaryWordsAvoidingEleven 6 + binaryWordsAvoidingEleven 5 ∧
    binaryWordsAvoidingEleven 8 = binaryWordsAvoidingEleven 7 + binaryWordsAvoidingEleven 6 ∧
    binaryWordsAvoidingEleven 9 = binaryWordsAvoidingEleven 8 + binaryWordsAvoidingEleven 7 ∧
    binaryWordsAvoidingEleven 10 = binaryWordsAvoidingEleven 9 + binaryWordsAvoidingEleven 8 ∧
    binaryWordsAvoidingEleven 11 = binaryWordsAvoidingEleven 10 + binaryWordsAvoidingEleven 9 := by
  native_decide

/-- The same table checked against the shifted Fibonacci values. -/
theorem binaryWordsAvoidingEleven_values :
    binaryWordsAvoidingEleven 0 = 1 ∧
    binaryWordsAvoidingEleven 1 = 2 ∧
    binaryWordsAvoidingEleven 2 = 3 ∧
    binaryWordsAvoidingEleven 3 = 5 ∧
    binaryWordsAvoidingEleven 4 = 8 ∧
    binaryWordsAvoidingEleven 5 = 13 ∧
    binaryWordsAvoidingEleven 6 = 21 ∧
    binaryWordsAvoidingEleven 7 = 34 ∧
    binaryWordsAvoidingEleven 8 = 55 ∧
    binaryWordsAvoidingEleven 9 = 89 ∧
    binaryWordsAvoidingEleven 10 = 144 ∧
    binaryWordsAvoidingEleven 11 = 233 := by
  native_decide

/-! ## Ternary words with no repeated letters -/

/-- Ternary words of length `n`, for `0 ≤ n ≤ 7`, in which no letter appears twice. -/
def ternaryWordsNoRepeatedLetters : Fin 8 → ℕ :=
  ![1, 3, 6, 6, 0, 0, 0, 0]

/-- Falling-factorial values for all-distinct ternary words. -/
theorem ternaryWordsNoRepeatedLetters_values :
    ternaryWordsNoRepeatedLetters 0 = 1 ∧
    ternaryWordsNoRepeatedLetters 1 = 3 ∧
    ternaryWordsNoRepeatedLetters 2 = 3 * 2 ∧
    ternaryWordsNoRepeatedLetters 3 = 3 * 2 * 1 ∧
    ternaryWordsNoRepeatedLetters 4 = 0 ∧
    ternaryWordsNoRepeatedLetters 5 = 0 ∧
    ternaryWordsNoRepeatedLetters 6 = 0 ∧
    ternaryWordsNoRepeatedLetters 7 = 0 := by
  native_decide

/-- Ternary Smirnov words of length `n`, for `0 ≤ n ≤ 11`, with no equal neighbors. -/
def ternaryWordsNoEqualNeighbors : Fin 12 → ℕ :=
  ![1, 3, 6, 12, 24, 48, 96, 192, 384, 768, 1536, 3072]

/-- Geometric progression after the initial empty word. -/
theorem ternaryWordsNoEqualNeighbors_values :
    ternaryWordsNoEqualNeighbors 0 = 1 ∧
    ternaryWordsNoEqualNeighbors 1 = 3 * 2 ^ 0 ∧
    ternaryWordsNoEqualNeighbors 2 = 3 * 2 ^ 1 ∧
    ternaryWordsNoEqualNeighbors 3 = 3 * 2 ^ 2 ∧
    ternaryWordsNoEqualNeighbors 4 = 3 * 2 ^ 3 ∧
    ternaryWordsNoEqualNeighbors 5 = 3 * 2 ^ 4 ∧
    ternaryWordsNoEqualNeighbors 6 = 3 * 2 ^ 5 ∧
    ternaryWordsNoEqualNeighbors 7 = 3 * 2 ^ 6 ∧
    ternaryWordsNoEqualNeighbors 8 = 3 * 2 ^ 7 ∧
    ternaryWordsNoEqualNeighbors 9 = 3 * 2 ^ 8 ∧
    ternaryWordsNoEqualNeighbors 10 = 3 * 2 ^ 9 ∧
    ternaryWordsNoEqualNeighbors 11 = 3 * 2 ^ 10 := by
  native_decide

/-! ## Lyndon words, primitive words, and necklaces -/

/-- Binary Lyndon words by length, for `0 ≤ n ≤ 11`; length zero is recorded as `0`. -/
def binaryLyndonWords : Fin 12 → ℕ :=
  ![0, 2, 1, 2, 3, 6, 9, 18, 30, 56, 99, 186]

/-- Primitive binary words by length, for `0 ≤ n ≤ 11`. -/
def primitiveBinaryWords : Fin 12 → ℕ :=
  ![0, 2, 2, 6, 12, 30, 54, 126, 240, 504, 990, 2046]

/-- Primitive binary words are `n` marked rotations of binary Lyndon words in these cases. -/
theorem primitiveBinaryWords_eq_length_mul_lyndon :
    primitiveBinaryWords 1 = 1 * binaryLyndonWords 1 ∧
    primitiveBinaryWords 2 = 2 * binaryLyndonWords 2 ∧
    primitiveBinaryWords 3 = 3 * binaryLyndonWords 3 ∧
    primitiveBinaryWords 4 = 4 * binaryLyndonWords 4 ∧
    primitiveBinaryWords 5 = 5 * binaryLyndonWords 5 ∧
    primitiveBinaryWords 6 = 6 * binaryLyndonWords 6 ∧
    primitiveBinaryWords 7 = 7 * binaryLyndonWords 7 ∧
    primitiveBinaryWords 8 = 8 * binaryLyndonWords 8 ∧
    primitiveBinaryWords 9 = 9 * binaryLyndonWords 9 ∧
    primitiveBinaryWords 10 = 10 * binaryLyndonWords 10 ∧
    primitiveBinaryWords 11 = 11 * binaryLyndonWords 11 := by
  native_decide

/-- Binary necklaces by length, for `0 ≤ n ≤ 11`; the empty necklace is counted once. -/
def binaryNecklaces : Fin 12 → ℕ :=
  ![1, 2, 3, 4, 6, 8, 14, 20, 36, 60, 108, 188]

/-- A necklace decomposes into a Lyndon word whose length divides the total length. -/
theorem binaryNecklaces_as_lyndon_divisor_sums :
    binaryNecklaces 1 = binaryLyndonWords 1 ∧
    binaryNecklaces 2 = binaryLyndonWords 1 + binaryLyndonWords 2 ∧
    binaryNecklaces 3 = binaryLyndonWords 1 + binaryLyndonWords 3 ∧
    binaryNecklaces 4 = binaryLyndonWords 1 + binaryLyndonWords 2 + binaryLyndonWords 4 ∧
    binaryNecklaces 5 = binaryLyndonWords 1 + binaryLyndonWords 5 ∧
    binaryNecklaces 6 =
      binaryLyndonWords 1 + binaryLyndonWords 2 + binaryLyndonWords 3 + binaryLyndonWords 6 ∧
    binaryNecklaces 7 = binaryLyndonWords 1 + binaryLyndonWords 7 ∧
    binaryNecklaces 8 =
      binaryLyndonWords 1 + binaryLyndonWords 2 + binaryLyndonWords 4 + binaryLyndonWords 8 ∧
    binaryNecklaces 9 = binaryLyndonWords 1 + binaryLyndonWords 3 + binaryLyndonWords 9 ∧
    binaryNecklaces 10 =
      binaryLyndonWords 1 + binaryLyndonWords 2 + binaryLyndonWords 5 + binaryLyndonWords 10 ∧
    binaryNecklaces 11 = binaryLyndonWords 1 + binaryLyndonWords 11 := by
  native_decide

/-- Ternary necklaces by length, for `0 ≤ n ≤ 8`; the empty necklace is counted once. -/
def ternaryNecklaces : Fin 9 → ℕ :=
  ![1, 3, 6, 11, 24, 51, 130, 315, 834]

/-- Small ternary necklace values from Burnside's cyclic orbit count. -/
theorem ternaryNecklaces_values :
    ternaryNecklaces 0 = 1 ∧
    ternaryNecklaces 1 = 3 ∧
    ternaryNecklaces 2 = 6 ∧
    ternaryNecklaces 3 = 11 ∧
    ternaryNecklaces 4 = 24 ∧
    ternaryNecklaces 5 = 51 ∧
    ternaryNecklaces 6 = 130 ∧
    ternaryNecklaces 7 = 315 ∧
    ternaryNecklaces 8 = 834 := by
  native_decide

/-! ## de Bruijn cycles -/

/--
Binary de Bruijn cycles of order `n`, for `0 ≤ n ≤ 5`, with order zero recorded
as `0`.  These are the normalized cyclic counts `2^(2^(n-1)-n)` for `n ≥ 1`.
-/
def binaryDeBruijnCycles : Fin 6 → ℕ :=
  ![0, 1, 1, 2, 16, 2048]

/-- The bounded table records existence of binary de Bruijn cycles through order five. -/
theorem binaryDeBruijnCycles_exist_small :
    0 < binaryDeBruijnCycles 1 ∧
    0 < binaryDeBruijnCycles 2 ∧
    0 < binaryDeBruijnCycles 3 ∧
    0 < binaryDeBruijnCycles 4 ∧
    0 < binaryDeBruijnCycles 5 := by
  native_decide

/-- Closed values for the same normalized Euler-circuit counts. -/
theorem binaryDeBruijnCycles_values :
    binaryDeBruijnCycles 1 = 1 ∧
    binaryDeBruijnCycles 2 = 1 ∧
    binaryDeBruijnCycles 3 = 2 ∧
    binaryDeBruijnCycles 4 = 16 ∧
    binaryDeBruijnCycles 5 = 2048 := by
  native_decide

end WordCombinatorics
