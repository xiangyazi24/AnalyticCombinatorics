import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace StirlingSaddlePoint

/-!
  Small bounded tables for Stirling-number families appearing around the
  saddle point treatment of Chapter VIII.
-/

/-! ## Signless Stirling numbers of the first kind -/

/-- The signless Stirling numbers `|s(n,k)|` for `0 <= n,k <= 8`. -/
def stirling1Table : Fin 9 -> Fin 9 -> ℕ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 2, 3, 1, 0, 0, 0, 0, 0],
    ![0, 6, 11, 6, 1, 0, 0, 0, 0],
    ![0, 24, 50, 35, 10, 1, 0, 0, 0],
    ![0, 120, 274, 225, 85, 15, 1, 0, 0],
    ![0, 720, 1764, 1624, 735, 175, 21, 1, 0],
    ![0, 5040, 13068, 13132, 6769, 1960, 322, 28, 1]
  ]

/-- Row sums of `|s(n,k)|`, namely `n!`, for `0 <= n <= 8`. -/
def stirling1RowSums : Fin 9 -> ℕ :=
  ![1, 1, 2, 6, 24, 120, 720, 5040, 40320]

/-! ## Stirling numbers of the second kind -/

/-- The Stirling numbers `S(n,k)` for `0 <= n,k <= 8`. -/
def stirling2Table : Fin 9 -> Fin 9 -> ℕ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 3, 1, 0, 0, 0, 0, 0],
    ![0, 1, 7, 6, 1, 0, 0, 0, 0],
    ![0, 1, 15, 25, 10, 1, 0, 0, 0],
    ![0, 1, 31, 90, 65, 15, 1, 0, 0],
    ![0, 1, 63, 301, 350, 140, 21, 1, 0],
    ![0, 1, 127, 966, 1701, 1050, 266, 28, 1]
  ]

/-- Bell numbers obtained as row sums of `S(n,k)`, for `0 <= n <= 8`. -/
def bellRowSums : Fin 9 -> ℕ :=
  ![1, 1, 2, 5, 15, 52, 203, 877, 4140]

/-! ## Cycle index counts -/

/-- Numerators of the univariate cycle-index specialization by number of cycles. -/
def cycleIndexCountTable : Fin 9 -> Fin 9 -> ℕ :=
  stirling1Table

/-- Factorial denominators for the normalized cycle index, for `0 <= n <= 8`. -/
def cycleIndexDenominators : Fin 9 -> ℕ :=
  ![1, 1, 2, 6, 24, 120, 720, 5040, 40320]

/-! ## Two restricted Stirling families -/

/-- The `r = 2` Stirling numbers of the second kind for `2 <= n <= 8`. -/
def r2Stirling2Table : Fin 7 -> Fin 9 -> ℕ :=
  ![
    ![0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 1, 0, 0, 0, 0, 0],
    ![0, 0, 4, 5, 1, 0, 0, 0, 0],
    ![0, 0, 8, 19, 9, 1, 0, 0, 0],
    ![0, 0, 16, 65, 55, 14, 1, 0, 0],
    ![0, 0, 32, 211, 285, 125, 20, 1, 0],
    ![0, 0, 64, 665, 1351, 910, 245, 27, 1]
  ]

/-- Associated Stirling numbers of the second kind with no singleton blocks. -/
def associatedStirling2Table : Fin 9 -> Fin 9 -> ℕ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 3, 0, 0, 0, 0, 0, 0],
    ![0, 1, 10, 0, 0, 0, 0, 0, 0],
    ![0, 1, 25, 15, 0, 0, 0, 0, 0],
    ![0, 1, 56, 105, 0, 0, 0, 0, 0],
    ![0, 1, 119, 490, 105, 0, 0, 0, 0]
  ]

/-- Row sums for associated set partitions with no singleton blocks. -/
def associatedBellRowSums : Fin 9 -> ℕ :=
  ![1, 0, 1, 1, 4, 11, 41, 162, 715]

/-! ## Bounded computation helpers -/

def rowSum9 (row : Fin 9 -> ℕ) : ℕ :=
  (Finset.univ : Finset (Fin 9)).sum row

def get9 (table : Fin 9 -> Fin 9 -> ℕ) (n k : ℕ) : ℕ :=
  if hn : n < 9 then
    if hk : k < 9 then
      table ⟨n, hn⟩ ⟨k, hk⟩
    else
      0
  else
    0

def getR2 (nOffset k : ℕ) : ℕ :=
  if hn : nOffset < 7 then
    if hk : k < 9 then
      r2Stirling2Table ⟨nOffset, hn⟩ ⟨k, hk⟩
    else
      0
  else
    0

/-! ## Native-decision checks -/

theorem stirling1_row_sums_0_to_8 :
    ∀ n : Fin 9, rowSum9 (stirling1Table n) = stirling1RowSums n := by
  native_decide

theorem stirling2_row_sums_0_to_8 :
    ∀ n : Fin 9, rowSum9 (stirling2Table n) = bellRowSums n := by
  native_decide

theorem stirling1_recurrence_0_to_7 :
    ∀ n : Fin 8, ∀ k : Fin 8,
      get9 stirling1Table ((n : ℕ) + 1) ((k : ℕ) + 1) =
        (n : ℕ) * get9 stirling1Table (n : ℕ) ((k : ℕ) + 1) +
          get9 stirling1Table (n : ℕ) (k : ℕ) := by
  native_decide

theorem stirling2_recurrence_0_to_7 :
    ∀ n : Fin 8, ∀ k : Fin 8,
      get9 stirling2Table ((n : ℕ) + 1) ((k : ℕ) + 1) =
        ((k : ℕ) + 1) * get9 stirling2Table (n : ℕ) ((k : ℕ) + 1) +
          get9 stirling2Table (n : ℕ) (k : ℕ) := by
  native_decide

theorem diagonal_entries_are_one :
    (∀ n : Fin 9, stirling1Table n n = 1) ∧
      (∀ n : Fin 9, stirling2Table n n = 1) := by
  native_decide

theorem zero_block_or_cycle_column :
    (∀ n : Fin 8, get9 stirling1Table ((n : ℕ) + 1) 0 = 0) ∧
      (∀ n : Fin 8, get9 stirling2Table ((n : ℕ) + 1) 0 = 0) := by
  native_decide

theorem cycle_index_counts_match_signless_stirling :
    cycleIndexCountTable = stirling1Table ∧
      cycleIndexDenominators = stirling1RowSums := by
  native_decide

theorem r2_stirling2_recurrence_2_to_7 :
    ∀ nOffset : Fin 6, ∀ k : Fin 6,
      getR2 ((nOffset : ℕ) + 1) ((k : ℕ) + 3) =
        ((k : ℕ) + 3) * getR2 (nOffset : ℕ) ((k : ℕ) + 3) +
          getR2 (nOffset : ℕ) ((k : ℕ) + 2) := by
  native_decide

theorem associated_stirling2_row_sums_0_to_8 :
    ∀ n : Fin 9, rowSum9 (associatedStirling2Table n) = associatedBellRowSums n := by
  native_decide

theorem associated_stirling2_no_too_many_blocks :
    ∀ n : Fin 9, ∀ k : Fin 4,
      get9 associatedStirling2Table (n : ℕ) ((k : ℕ) + 5) = 0 := by
  native_decide

end StirlingSaddlePoint
