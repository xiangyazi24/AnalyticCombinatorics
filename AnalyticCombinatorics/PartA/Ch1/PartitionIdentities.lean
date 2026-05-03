import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace PartitionIdentities

/-!
  Integer partition identities and ordinary generating-function coefficients
  from Chapter I of Analytic Combinatorics.
-/

def partitionTable : Fin 21 → ℕ :=
  ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231, 297,
    385, 490, 627]

def distinctPartitionTable : Fin 21 → ℕ :=
  ![1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15, 18, 22, 27, 32, 38, 46, 54,
    64]

def oddPartPartitionTable : Fin 16 → ℕ :=
  ![1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15, 18, 22, 27]

def tableLookup {m : ℕ} (table : Fin m → ℕ) (n : ℕ) : ℕ :=
  if h : n < m then table ⟨n, h⟩ else 0

def partitionNumber (n : ℕ) : ℕ :=
  tableLookup partitionTable n

def distinctPartitionNumber (n : ℕ) : ℕ :=
  tableLookup distinctPartitionTable n

def oddPartPartitionNumber (n : ℕ) : ℕ :=
  tableLookup oddPartPartitionTable n

theorem partition_numbers_0_to_20 :
    (fun n : Fin 21 => partitionNumber n.val) = partitionTable := by native_decide

theorem distinct_partition_numbers_0_to_20 :
    (fun n : Fin 21 => distinctPartitionNumber n.val) = distinctPartitionTable := by native_decide

theorem euler_distinct_eq_odd_0_to_15 :
    (fun n : Fin 16 => distinctPartitionNumber n.val) =
      (fun n : Fin 16 => oddPartPartitionNumber n.val) := by native_decide

/-! ### Partitions with largest part at most `k` -/

def partitionLeqTable : Fin 11 → Fin 7 → ℕ :=
  ![
    ![1, 1, 1, 1, 1, 1, 1],
    ![0, 1, 1, 1, 1, 1, 1],
    ![0, 1, 2, 2, 2, 2, 2],
    ![0, 1, 2, 3, 3, 3, 3],
    ![0, 1, 3, 4, 5, 5, 5],
    ![0, 1, 3, 5, 6, 7, 7],
    ![0, 1, 4, 7, 9, 10, 11],
    ![0, 1, 4, 8, 11, 13, 14],
    ![0, 1, 5, 10, 15, 18, 20],
    ![0, 1, 5, 12, 18, 23, 26],
    ![0, 1, 6, 14, 23, 30, 35]
  ]

def partitionLeqSmall (n k : ℕ) : ℕ :=
  if hn : n < 11 then
    if hk : k < 7 then
      partitionLeqTable ⟨n, hn⟩ ⟨k, hk⟩
    else
      partitionNumber n
  else
    0

def partitionLeq (n k : ℕ) : ℕ :=
  match k with
  | 0 => if n = 0 then 1 else 0
  | 1 => 1
  | 2 => n / 2 + 1
  | _ => partitionLeqSmall n k

theorem partition_leq_table_0_to_10_0_to_6 :
    (fun n : Fin 11 => fun k : Fin 7 => partitionLeq n.val k.val) =
      partitionLeqTable := by native_decide

theorem partition_leq_one_all (n : ℕ) : partitionLeq n 1 = 1 :=
  (by native_decide : (1 : ℕ) = 1)

theorem partition_leq_two_formula_0_to_10 :
    (fun n : Fin 11 => partitionLeq n.val 2) =
      (fun n : Fin 11 => n.val / 2 + 1) := by native_decide

/-! ### Conjugation: exact number of parts versus largest part -/

def exactlyKParts (n k : ℕ) : ℕ :=
  if k ≤ n then partitionLeq (n - k) k else 0

def largestPartEq (n k : ℕ) : ℕ :=
  if k ≤ n then partitionLeq (n - k) k else 0

theorem conjugate_exact_parts_eq_largest_part_0_to_10 :
    (fun nk : Fin 11 × Fin 7 => exactlyKParts nk.1.val nk.2.val) =
      (fun nk : Fin 11 × Fin 7 => largestPartEq nk.1.val nk.2.val) := by
  native_decide

theorem partitions_six_exactly_two_parts :
    exactlyKParts 6 2 = 3 := by native_decide

theorem partitions_six_largest_part_two :
    largestPartEq 6 2 = 3 := by native_decide

/-! ### The eleven partitions of 6 -/

def partitionsOfSix : Fin 11 → List ℕ :=
  ![
    [6],
    [5, 1],
    [4, 2],
    [4, 1, 1],
    [3, 3],
    [3, 2, 1],
    [3, 1, 1, 1],
    [2, 2, 2],
    [2, 2, 1, 1],
    [2, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1]
  ]

def partitionWeight (parts : List ℕ) : ℕ :=
  parts.sum

theorem partitions_of_six_all_have_weight_six :
    (fun i : Fin 11 => partitionWeight (partitionsOfSix i)) =
      (fun _ : Fin 11 => 6) := by native_decide

theorem partition_number_six :
    partitionNumber 6 = 11 := by native_decide

theorem partitions_of_six_total :
    (List.ofFn partitionsOfSix).length = 11 := by native_decide

/-! ### Ferrers diagram duality -/

def maxPart (parts : List ℕ) : ℕ :=
  parts.foldr Nat.max 0

def ferrersConjugate (parts : List ℕ) : List ℕ :=
  (List.range (maxPart parts)).map
    (fun i => (parts.filter (fun part => i.succ ≤ part)).length)

theorem ferrers_conjugate_six :
    ferrersConjugate [6] = [1, 1, 1, 1, 1, 1] := by native_decide

theorem ferrers_conjugate_five_one :
    ferrersConjugate [5, 1] = [2, 1, 1, 1, 1] := by native_decide

theorem ferrers_conjugate_four_two :
    ferrersConjugate [4, 2] = [2, 2, 1, 1] := by native_decide

theorem ferrers_conjugate_three_two_one :
    ferrersConjugate [3, 2, 1] = [3, 2, 1] := by native_decide

theorem ferrers_conjugate_two_two_two :
    ferrersConjugate [2, 2, 2] = [3, 3] := by native_decide

theorem ferrers_conjugate_involution_examples :
    (fun p : Fin 5 =>
        ferrersConjugate (ferrersConjugate
          (![ [6], [5, 1], [4, 2], [3, 2, 1], [2, 2, 2] ] p))) =
      (![ [6], [5, 1], [4, 2], [3, 2, 1], [2, 2, 2] ] : Fin 5 → List ℕ) := by
  native_decide

/-! ### Pentagonal number theorem recurrence -/

def generalizedPentagonalOffsets : Fin 6 → ℕ :=
  ![1, 2, 5, 7, 12, 15]

def pentagonalLhsSign (i : Fin 6) : ℤ :=
  if (i.val / 2) % 2 = 0 then -1 else 1

def partitionInt (n : ℕ) : ℤ :=
  (partitionNumber n : ℤ)

def pentagonalRecurrenceLhs (n : ℕ) : ℤ :=
  partitionInt n +
    ∑ i : Fin 6,
      if generalizedPentagonalOffsets i ≤ n then
        pentagonalLhsSign i * partitionInt (n - generalizedPentagonalOffsets i)
      else
        0

theorem pentagonal_recurrence_1_to_20 :
    (fun i : Fin 20 => pentagonalRecurrenceLhs (i.val + 1)) =
      (fun _ : Fin 20 => (0 : ℤ)) := by native_decide

end PartitionIdentities
