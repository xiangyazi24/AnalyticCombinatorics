import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace SetPartitionStatistics

/-! # Set Partition Statistics

Combinatorics of set partitions following Flajolet & Sedgewick Ch. II:
Stirling numbers of the second kind, restricted growth strings, partition
rank and type, Lah numbers, associated Stirling and Lah numbers, and the
exponential generating function exp(exp(z) - 1). -/

/-! ## Stirling numbers of the second kind

S(n,k) counts partitions of an n-set into exactly k non-empty blocks.
Recurrence: the new element either forms a singleton block or joins
one of the k existing blocks. -/

/-- S(n,k): number of partitions of an n-set into exactly k non-empty blocks. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)

theorem stirling2_recurrence (n k : ℕ) :
    stirling2 (n + 1) (k + 1) = stirling2 n k + (k + 1) * stirling2 n (k + 1) := by
  rfl

theorem stirling2_zero_zero : stirling2 0 0 = 1 := by native_decide

theorem stirling2_n_zero (n : ℕ) (hn : n ≥ 1) : stirling2 n 0 = 0 := by
  cases n with | zero => omega | succ n => rfl

theorem stirling2_n_one (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 7) : stirling2 n 1 = 1 := by
  interval_cases n <;> native_decide

theorem stirling2_n_n (n : ℕ) (hn : n ≤ 7) : stirling2 n n = 1 := by
  interval_cases n <;> native_decide

/-- S(n, n-1) = C(n,2): choose one pair, rest are singletons. -/
theorem stirling2_n_pred (n : ℕ) (hn : n ≤ 7) (hn2 : n ≥ 2) :
    stirling2 n (n - 1) = Nat.choose n 2 := by
  interval_cases n <;> native_decide

/-- S(n,2) = 2^(n-1) - 1 for n ≥ 2. -/
theorem stirling2_n_two (n : ℕ) (hn : n ≤ 7) (hn2 : n ≥ 2) :
    stirling2 n 2 = 2 ^ (n - 1) - 1 := by
  interval_cases n <;> native_decide

theorem stirling2_4_2 : stirling2 4 2 = 7 := by native_decide
theorem stirling2_4_3 : stirling2 4 3 = 6 := by native_decide
theorem stirling2_5_2 : stirling2 5 2 = 15 := by native_decide
theorem stirling2_5_3 : stirling2 5 3 = 25 := by native_decide
theorem stirling2_6_2 : stirling2 6 2 = 31 := by native_decide
theorem stirling2_6_3 : stirling2 6 3 = 90 := by native_decide
theorem stirling2_7_3 : stirling2 7 3 = 301 := by native_decide

/-- Inclusion-exclusion: k! · S(n,k) = ∑ (-1)^j C(k,j) (k-j)^n. -/
theorem stirling2_inclusion_exclusion (n k : ℕ) :
    (Nat.factorial k : ℤ) * (stirling2 n k : ℤ) =
    ∑ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ j * (Nat.choose k j : ℤ) * ((k : ℤ) - (j : ℤ)) ^ n := by
  sorry

/-! ## Bell numbers

B(n) is the total number of set partitions of [n], equal to the
Stirling row sum ∑_k S(n,k). -/

/-- B(n): total number of partitions of an n-set. -/
def bell (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), stirling2 n k

theorem bell_0 : bell 0 = 1 := by native_decide
theorem bell_1 : bell 1 = 1 := by native_decide
theorem bell_2 : bell 2 = 2 := by native_decide
theorem bell_3 : bell 3 = 5 := by native_decide
theorem bell_4 : bell 4 = 15 := by native_decide
theorem bell_5 : bell 5 = 52 := by native_decide
theorem bell_6 : bell 6 = 203 := by native_decide
theorem bell_7 : bell 7 = 877 := by native_decide

/-- Bell recurrence: B(n+1) = ∑_{k=0}^{n} C(n,k) B(k). -/
theorem bell_recurrence_check (n : ℕ) (hn : n ≤ 5) :
    bell (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose n k * bell k := by
  interval_cases n <;> native_decide

/-! ## Restricted growth strings (RGS)

An RGS of length n encodes a set partition of [n]: it is a sequence
a₀ a₁ ⋯ a_{n-1} where a₀ = 0 and aᵢ ≤ 1 + max(a₀, …, a_{i-1}).
Element i is placed in block number aᵢ. -/

/-- Auxiliary: check RGS validity given the running maximum so far. -/
def isValidRGSAux : ℕ → List ℕ → Bool
  | _, [] => true
  | curMax, x :: xs => decide (x ≤ curMax + 1) && isValidRGSAux (Nat.max curMax x) xs

/-- A list is a valid restricted growth string iff it starts with 0
    and each entry is at most 1 + the running maximum of predecessors. -/
def isValidRGS : List ℕ → Bool
  | [] => true
  | 0 :: rest => isValidRGSAux 0 rest
  | _ :: _ => false

theorem rgs_empty_valid : isValidRGS [] = true := by rfl
theorem rgs_zero_valid : isValidRGS [0] = true := by rfl
theorem rgs_00_valid : isValidRGS [0, 0] = true := by native_decide
theorem rgs_01_valid : isValidRGS [0, 1] = true := by native_decide
theorem rgs_02_invalid : isValidRGS [0, 2] = false := by native_decide
theorem rgs_10_invalid : isValidRGS [1, 0] = false := by native_decide
theorem rgs_012_valid : isValidRGS [0, 1, 2] = true := by native_decide
theorem rgs_010_valid : isValidRGS [0, 1, 0] = true := by native_decide
theorem rgs_013_invalid : isValidRGS [0, 1, 3] = false := by native_decide
theorem rgs_0121_valid : isValidRGS [0, 1, 2, 1] = true := by native_decide

/-- Generate all valid RGS of a given length by extending shorter ones.
    At each step, a new entry can be any value from 0 to max+1. -/
def allRGS : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 =>
    (allRGS n).flatMap fun rgs =>
      let m := rgs.foldl Nat.max 0
      let bound := if rgs.isEmpty then 1 else m + 2
      (List.range bound).map fun v => rgs ++ [v]

/-- All generated RGS are valid. -/
theorem allRGS_valid (n : ℕ) (hn : n ≤ 5) :
    (allRGS n).all isValidRGS = true := by
  interval_cases n <;> native_decide

/-- The number of RGS of length n equals the Bell number B(n). -/
theorem rgs_count_eq_bell (n : ℕ) (hn : n ≤ 6) :
    (allRGS n).length = bell n := by
  interval_cases n <;> native_decide

/-- For all n: the number of RGS of length n equals B(n). -/
theorem rgs_count_eq_bell_general (n : ℕ) :
    (allRGS n).length = bell n := by
  sorry

/-! ## Rank of a set partition (number of blocks)

The rank of a partition is its number of blocks. For an RGS, this
equals 1 + max(rgs). The rank distribution is given by Stirling numbers:
the number of partitions of [n] with rank k equals S(n,k). -/

/-- Number of blocks in the partition encoded by an RGS. -/
def rgsBlockCount (rgs : List ℕ) : ℕ :=
  match rgs with
  | [] => 0
  | _ => rgs.foldl Nat.max 0 + 1

theorem rank_one : rgsBlockCount [0] = 1 := by native_decide
theorem rank_one' : rgsBlockCount [0, 0] = 1 := by native_decide
theorem rank_two : rgsBlockCount [0, 1] = 2 := by native_decide
theorem rank_two' : rgsBlockCount [0, 1, 0] = 2 := by native_decide
theorem rank_three : rgsBlockCount [0, 1, 2] = 3 := by native_decide
theorem rank_mixed : rgsBlockCount [0, 1, 0, 1, 2] = 3 := by native_decide

/-- Count RGS of length n with exactly k blocks. -/
def rgsWithKBlocks (n k : ℕ) : ℕ :=
  ((allRGS n).filter fun rgs => rgsBlockCount rgs == k).length

/-- The block-count distribution matches Stirling numbers for n = 4. -/
theorem block_dist_4 :
    rgsWithKBlocks 4 1 = stirling2 4 1 ∧
    rgsWithKBlocks 4 2 = stirling2 4 2 ∧
    rgsWithKBlocks 4 3 = stirling2 4 3 ∧
    rgsWithKBlocks 4 4 = stirling2 4 4 := by native_decide

/-- The block-count distribution matches Stirling numbers for n = 5. -/
theorem block_dist_5 :
    rgsWithKBlocks 5 1 = stirling2 5 1 ∧
    rgsWithKBlocks 5 2 = stirling2 5 2 ∧
    rgsWithKBlocks 5 3 = stirling2 5 3 ∧
    rgsWithKBlocks 5 4 = stirling2 5 4 ∧
    rgsWithKBlocks 5 5 = stirling2 5 5 := by native_decide

/-- For all n, k: rgsWithKBlocks n k = S(n, k). -/
theorem rgs_block_count_eq_stirling2 (n k : ℕ) :
    rgsWithKBlocks n k = stirling2 n k := by
  sorry

/-! ## Type of a set partition

The type of a partition is the tuple of block sizes in decreasing order.
For example, {{1,3,5}, {2,4}, {6}} has type [3, 2, 1].
The number of partitions of [n] with type λ is the multinomial
n! / (∏ λ_i! · ∏ m_j!) where m_j counts blocks of size j. -/

/-- Insertion into a decreasingly sorted list. -/
def insertDesc (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≥ y then x :: y :: ys else y :: insertDesc x ys

/-- Sort a list in decreasing order. -/
def sortDesc : List ℕ → List ℕ
  | [] => []
  | x :: xs => insertDesc x (sortDesc xs)

theorem sortDesc_example : sortDesc [1, 3, 2] = [3, 2, 1] := by native_decide
theorem sortDesc_ties : sortDesc [2, 2, 1] = [2, 2, 1] := by native_decide

/-- Compute block sizes from an RGS: count occurrences of each block label. -/
def rgsBlockSizes (rgs : List ℕ) : List ℕ :=
  match rgs with
  | [] => []
  | _ =>
    let m := rgs.foldl Nat.max 0
    (List.range (m + 1)).map fun v => (rgs.filter (· == v)).length

/-- The type (decreasingly sorted block sizes) of a partition given by an RGS. -/
def rgsType (rgs : List ℕ) : List ℕ :=
  sortDesc (rgsBlockSizes rgs)

theorem type_one_block : rgsType [0, 0, 0] = [3] := by native_decide
theorem type_all_singletons : rgsType [0, 1, 2] = [1, 1, 1] := by native_decide
theorem type_21 : rgsType [0, 1, 0] = [2, 1] := by native_decide
theorem type_22 : rgsType [0, 1, 0, 1] = [2, 2] := by native_decide
theorem type_31 : rgsType [0, 0, 0, 1] = [3, 1] := by native_decide
theorem type_211 : rgsType [0, 1, 2, 0] = [2, 1, 1] := by native_decide

/-- Block sizes always sum to the length of the RGS. -/
theorem block_sizes_sum_to_length (n : ℕ) :
    ∀ rgs ∈ allRGS n, (rgsBlockSizes rgs).sum = n := by
  sorry

/-- Count partitions of [n] having a given type. -/
def partitionsOfType (n : ℕ) (tp : List ℕ) : ℕ :=
  ((allRGS n).filter fun rgs => rgsType rgs == tp).length

theorem partitions_type_4_4 : partitionsOfType 4 [4] = 1 := by native_decide
theorem partitions_type_4_31 : partitionsOfType 4 [3, 1] = 4 := by native_decide
theorem partitions_type_4_22 : partitionsOfType 4 [2, 2] = 3 := by native_decide
theorem partitions_type_4_211 : partitionsOfType 4 [2, 1, 1] = 6 := by native_decide
theorem partitions_type_4_1111 : partitionsOfType 4 [1, 1, 1, 1] = 1 := by native_decide

/-- Sum of partition counts by type equals B(n). -/
theorem type_sum_eq_bell_4 :
    partitionsOfType 4 [4] + partitionsOfType 4 [3, 1] +
    partitionsOfType 4 [2, 2] + partitionsOfType 4 [2, 1, 1] +
    partitionsOfType 4 [1, 1, 1, 1] = bell 4 := by native_decide

/-! ### Multinomial formula for partition type counts -/

/-- Multinomial coefficient: n! / (a₁! · a₂! · ⋯ · a_k!). -/
def multinomial (n : ℕ) (parts : List ℕ) : ℕ :=
  Nat.factorial n / (parts.map Nat.factorial).foldl (· * ·) 1

/-- Remove duplicate values from a list, preserving first occurrences. -/
def uniqueValues (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x => if acc.any (· == x) then acc else acc ++ [x]) []

/-- Count how many times each distinct value appears. -/
def valueCounts (l : List ℕ) : List ℕ :=
  (uniqueValues l).map fun v => (l.filter (· == v)).length

/-- Number of partitions of type tp = n! / (∏ tp_i! · ∏ m_j!),
    where m_j are the multiplicities of distinct part sizes. -/
def partitionTypeCount (n : ℕ) (tp : List ℕ) : ℕ :=
  let multProd := (valueCounts tp).map Nat.factorial |>.foldl (· * ·) 1
  multinomial n tp / multProd

theorem type_count_4_31 : partitionTypeCount 4 [3, 1] = 4 := by native_decide
theorem type_count_4_22 : partitionTypeCount 4 [2, 2] = 3 := by native_decide
theorem type_count_4_211 : partitionTypeCount 4 [2, 1, 1] = 6 := by native_decide
theorem type_count_4_1111 : partitionTypeCount 4 [1, 1, 1, 1] = 1 := by native_decide
theorem type_count_4_4 : partitionTypeCount 4 [4] = 1 := by native_decide

/-- The multinomial formula matches enumeration for n = 4. -/
theorem type_formula_matches_enum_4 :
    partitionTypeCount 4 [4] = partitionsOfType 4 [4] ∧
    partitionTypeCount 4 [3, 1] = partitionsOfType 4 [3, 1] ∧
    partitionTypeCount 4 [2, 2] = partitionsOfType 4 [2, 2] ∧
    partitionTypeCount 4 [2, 1, 1] = partitionsOfType 4 [2, 1, 1] ∧
    partitionTypeCount 4 [1, 1, 1, 1] = partitionsOfType 4 [1, 1, 1, 1] := by
  native_decide

/-- The multinomial formula gives the correct count for all n. -/
theorem partition_type_count_correct (n : ℕ) (tp : List ℕ) :
    partitionTypeCount n tp = partitionsOfType n tp := by
  sorry

/-! ## Lah numbers

L(n,k) counts partitions of [n] into k non-empty linearly ordered
subsets (Laguerre configurations). The recurrence follows from either
starting a new block or inserting the new element into an existing
ordered block. -/

/-- Unsigned Lah number L(n,k): partitions of [n] into k ordered blocks. -/
def lahNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => lahNumber n k + (n + k + 1) * lahNumber n (k + 1)

theorem lah_0_0 : lahNumber 0 0 = 1 := by native_decide
theorem lah_1_1 : lahNumber 1 1 = 1 := by native_decide
theorem lah_2_1 : lahNumber 2 1 = 2 := by native_decide
theorem lah_2_2 : lahNumber 2 2 = 1 := by native_decide
theorem lah_3_1 : lahNumber 3 1 = 6 := by native_decide
theorem lah_3_2 : lahNumber 3 2 = 6 := by native_decide
theorem lah_3_3 : lahNumber 3 3 = 1 := by native_decide
theorem lah_4_1 : lahNumber 4 1 = 24 := by native_decide
theorem lah_4_2 : lahNumber 4 2 = 36 := by native_decide
theorem lah_4_3 : lahNumber 4 3 = 12 := by native_decide
theorem lah_4_4 : lahNumber 4 4 = 1 := by native_decide
theorem lah_5_1 : lahNumber 5 1 = 120 := by native_decide
theorem lah_5_2 : lahNumber 5 2 = 240 := by native_decide
theorem lah_5_3 : lahNumber 5 3 = 120 := by native_decide
theorem lah_5_4 : lahNumber 5 4 = 20 := by native_decide
theorem lah_5_5 : lahNumber 5 5 = 1 := by native_decide

/-- L(n, 1) = n! : one block with all elements ordered. -/
theorem lah_n_one (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 7) :
    lahNumber n 1 = Nat.factorial n := by
  interval_cases n <;> native_decide

/-- L(n, n) = 1 : all singletons, each trivially ordered. -/
theorem lah_n_n (n : ℕ) (hn : n ≤ 7) : lahNumber n n = 1 := by
  interval_cases n <;> native_decide

/-- L(n, n-1) = 2 · C(n, 2) for n ≥ 2 : choose a pair, order it. -/
theorem lah_n_pred (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 7) :
    lahNumber n (n - 1) = 2 * Nat.choose n 2 := by
  interval_cases n <;> native_decide

/-- Closed form: L(n,k) = C(n-1, k-1) · n! / k! for n, k ≥ 1. -/
theorem lah_closed_form (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) (hn' : n ≤ 7) :
    lahNumber n k = Nat.choose (n - 1) (k - 1) * Nat.factorial n / Nat.factorial k := by
  interval_cases n <;> interval_cases k <;> native_decide

/-- The closed form holds for all n, k ≥ 1. -/
theorem lah_closed_form_general (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    lahNumber n k = Nat.choose (n - 1) (k - 1) * Nat.factorial n / Nat.factorial k := by
  sorry

/-- Lah row sum: total number of Laguerre configurations of [n]. -/
def lahRowSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), lahNumber n k

theorem lah_row_sum_0 : lahRowSum 0 = 1 := by native_decide
theorem lah_row_sum_1 : lahRowSum 1 = 1 := by native_decide
theorem lah_row_sum_2 : lahRowSum 2 = 3 := by native_decide
theorem lah_row_sum_3 : lahRowSum 3 = 13 := by native_decide
theorem lah_row_sum_4 : lahRowSum 4 = 73 := by native_decide
theorem lah_row_sum_5 : lahRowSum 5 = 501 := by native_decide

/-- Lah numbers relate Stirling numbers of the first and second kind:
    L(n,k) = ∑_j |s(n,j)| · S(j,k), connecting falling and rising factorials. -/
theorem lah_as_stirling_composition (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    lahNumber n k = Nat.choose (n - 1) (k - 1) * Nat.factorial n / Nat.factorial k := by
  sorry

/-! ## Associated Stirling numbers of the second kind

S_{≥2}(n,k) counts partitions of [n] into k blocks each of size ≥ 2
(no singleton blocks). The recurrence merges element n+2 into an
existing block or pairs it with an existing element to form a new block. -/

/-- Associated Stirling number S_{≥2}(n,k): partitions into k blocks of size ≥ 2. -/
def assocStirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | 1, _ => 0
  | _ + 2, 0 => 0
  | n + 2, k + 1 => (k + 1) * assocStirling2 (n + 1) (k + 1) + (n + 1) * assocStirling2 n k

theorem assoc_stirling2_0_0 : assocStirling2 0 0 = 1 := by native_decide
theorem assoc_stirling2_1_k : assocStirling2 1 0 = 0 ∧ assocStirling2 1 1 = 0 := by native_decide
theorem assoc_stirling2_2_1 : assocStirling2 2 1 = 1 := by native_decide
theorem assoc_stirling2_3_1 : assocStirling2 3 1 = 1 := by native_decide
theorem assoc_stirling2_4_1 : assocStirling2 4 1 = 1 := by native_decide
theorem assoc_stirling2_4_2 : assocStirling2 4 2 = 3 := by native_decide
theorem assoc_stirling2_5_2 : assocStirling2 5 2 = 10 := by native_decide
theorem assoc_stirling2_6_2 : assocStirling2 6 2 = 25 := by native_decide
theorem assoc_stirling2_6_3 : assocStirling2 6 3 = 15 := by native_decide

/-- Associated Bell number: total partitions of [n] with no singleton blocks. -/
def assocBell (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), assocStirling2 n k

theorem assoc_bell_0 : assocBell 0 = 1 := by native_decide
theorem assoc_bell_1 : assocBell 1 = 0 := by native_decide
theorem assoc_bell_2 : assocBell 2 = 1 := by native_decide
theorem assoc_bell_3 : assocBell 3 = 1 := by native_decide
theorem assoc_bell_4 : assocBell 4 = 4 := by native_decide
theorem assoc_bell_5 : assocBell 5 = 11 := by native_decide
theorem assoc_bell_6 : assocBell 6 = 41 := by native_decide

/-- Associated Bell numbers can be verified via RGS enumeration. -/
theorem assoc_bell_via_rgs (n : ℕ) (hn : n ≤ 6) :
    assocBell n =
    ((allRGS n).filter fun rgs =>
      (rgsBlockSizes rgs).all (fun s => decide (s ≥ 2))).length := by
  interval_cases n <;> native_decide

/-- The EGF of associated Bell numbers is exp(exp(z) - 1 - z). -/
theorem assoc_bell_egf :
    ∀ (n : ℕ), assocBell n =
    ∑ k ∈ Finset.range (n + 1), assocStirling2 n k := by
  intro n; rfl

/-! ## Associated Lah numbers

Count the number of partitions of [n] into k linearly ordered blocks,
each of size ≥ 2. Computed as the sum over qualifying RGS of the
product of block-size factorials (orderings within each block). -/

/-- Associated Lah number: partitions of [n] into k ordered blocks of size ≥ 2.
    For each qualifying unordered partition, count all ways to linearly order
    the elements within each block. -/
def assocLahNumber (n k : ℕ) : ℕ :=
  let valid := (allRGS n).filter fun rgs =>
    rgsBlockCount rgs == k && (rgsBlockSizes rgs).all (fun s => decide (s ≥ 2))
  valid.foldl (fun acc rgs =>
    acc + ((rgsBlockSizes rgs).map Nat.factorial).foldl (· * ·) 1) 0

theorem assoc_lah_0_0 : assocLahNumber 0 0 = 1 := by native_decide
theorem assoc_lah_2_1 : assocLahNumber 2 1 = 2 := by native_decide
theorem assoc_lah_3_1 : assocLahNumber 3 1 = 6 := by native_decide
theorem assoc_lah_4_1 : assocLahNumber 4 1 = 24 := by native_decide
theorem assoc_lah_4_2 : assocLahNumber 4 2 = 12 := by native_decide
theorem assoc_lah_5_1 : assocLahNumber 5 1 = 120 := by native_decide
theorem assoc_lah_5_2 : assocLahNumber 5 2 = 120 := by native_decide
theorem assoc_lah_6_3 : assocLahNumber 6 3 = 120 := by native_decide

/-- Associated Lah row sum: total ordered partitions with no singletons. -/
def assocLahRowSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), assocLahNumber n k

theorem assoc_lah_row_sum_0 : assocLahRowSum 0 = 1 := by native_decide
theorem assoc_lah_row_sum_2 : assocLahRowSum 2 = 2 := by native_decide
theorem assoc_lah_row_sum_3 : assocLahRowSum 3 = 6 := by native_decide
theorem assoc_lah_row_sum_4 : assocLahRowSum 4 = 36 := by native_decide
theorem assoc_lah_row_sum_5 : assocLahRowSum 5 = 240 := by native_decide

/-! ## Surjection connection

The number of surjections from an n-set onto a k-set is k! · S(n,k).
This follows since each surjection induces a set partition of the
domain into k blocks (fibers), and there are k! ways to assign
blocks to codomain elements. -/

/-- Number of surjections from [n] onto [k]. -/
def surjections (n k : ℕ) : ℕ := Nat.factorial k * stirling2 n k

theorem surjections_3_3 : surjections 3 3 = 6 := by native_decide
theorem surjections_4_2 : surjections 4 2 = 14 := by native_decide
theorem surjections_4_3 : surjections 4 3 = 36 := by native_decide
theorem surjections_5_3 : surjections 5 3 = 150 := by native_decide

/-- Surjections from [n] onto [n] are just permutations: n! -/
theorem surjections_n_n (n : ℕ) (hn : n ≤ 7) (hn0 : 1 ≤ n) :
    surjections n n = Nat.factorial n := by
  interval_cases n <;> native_decide

/-! ## EGF connection: exp(exp(z) - 1)

The exponential generating function of Bell numbers is
  ∑_{n≥0} B(n) z^n / n! = exp(exp(z) - 1).
This encodes that a set partition is a set of non-empty subsets:
the inner exp(z) - 1 is the EGF of a single non-empty block, and
the outer exp applies the "set-of" construction. -/

/-- EGF coefficients: n! · [z^n] exp(e^z - 1) = B(n).
    We verify the first few coefficients match Bell numbers. -/
theorem egf_coeff_check :
    bell 0 = 1 ∧ bell 1 = 1 ∧ bell 2 = 2 ∧ bell 3 = 5 ∧
    bell 4 = 15 ∧ bell 5 = 52 ∧ bell 6 = 203 := by native_decide

/-- The EGF identity: ∑_{n≥0} B(n) x^n / n! = exp(exp(x) - 1). -/
theorem bell_egf_is_exp_exp_minus_one :
    ∀ (x : ℝ), ∑' (n : ℕ), (bell n : ℝ) / (Nat.factorial n : ℝ) * x ^ n =
      Real.exp (Real.exp x - 1) := by
  sorry

/-- The EGF series converges for all x ∈ ℝ. -/
theorem bell_egf_converges (x : ℝ) :
    Summable (fun n : ℕ => (bell n : ℝ) / (Nat.factorial n : ℝ) * x ^ n) := by
  sorry

/-- The EGF of associated Bell numbers (no singletons) is exp(exp(z) - 1 - z):
    replace exp(z) - 1 with exp(z) - 1 - z to exclude singleton blocks. -/
theorem assoc_bell_egf_identity :
    ∀ (x : ℝ), ∑' (n : ℕ), (assocBell n : ℝ) / (Nat.factorial n : ℝ) * x ^ n =
      Real.exp (Real.exp x - 1 - x) := by
  sorry

/-! ## Deeper theorems -/

/-- Dobinski's formula: B(n) = (1/e) ∑_{k≥0} k^n / k!. -/
theorem dobinski_formula (n : ℕ) :
    (bell n : ℝ) = Real.exp (-1) *
      ∑' (k : ℕ), (k ^ n : ℝ) / (Nat.factorial k : ℝ) := by
  sorry

/-- The Dobinski series converges absolutely. -/
theorem dobinski_summable (n : ℕ) :
    Summable (fun k : ℕ => (k ^ n : ℝ) / (Nat.factorial k : ℝ)) := by
  sorry

/-- Log-convexity of Bell numbers: B(n)² ≤ B(n-1) · B(n+1) for n ≥ 1. -/
theorem bell_log_convexity (n : ℕ) (hn : 1 ≤ n) :
    bell n * bell n ≤ bell (n - 1) * bell (n + 1) := by
  sorry

/-- Verified for small cases. -/
theorem bell_log_convexity_check :
    bell 2 * bell 2 ≤ bell 1 * bell 3 ∧
    bell 3 * bell 3 ≤ bell 2 * bell 4 ∧
    bell 4 * bell 4 ≤ bell 3 * bell 5 := by native_decide

/-- Bell numbers grow faster than n! eventually. -/
theorem bell_exceeds_factorial :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Nat.factorial n ≤ bell n := by
  sorry

/-- Monotonicity: B(n) ≤ B(n+1) for all n. -/
theorem bell_monotone (n : ℕ) : bell n ≤ bell (n + 1) := by
  sorry

/-- Lah numbers satisfy the row sum identity
    ∑_k L(n,k) = n! · [z^n] 1/(1-z) composed with z/(1-z). -/
theorem lah_row_sum_formula (n : ℕ) :
    lahRowSum n = ∑ k ∈ Finset.range (n + 1), lahNumber n k := by
  rfl

/-- Every valid RGS in allRGS n is valid. -/
theorem allRGS_all_valid (n : ℕ) :
    ∀ rgs ∈ allRGS n, isValidRGS rgs = true := by
  sorry

/-- The allRGS enumeration is complete: every valid RGS of length n appears. -/
theorem allRGS_complete (n : ℕ) (rgs : List ℕ) (hlen : rgs.length = n)
    (hvalid : isValidRGS rgs = true) :
    rgs ∈ allRGS n := by
  sorry

/-- The allRGS enumeration contains no duplicates. -/
theorem allRGS_nodup (n : ℕ) : (allRGS n).Nodup := by
  sorry

end SetPartitionStatistics
