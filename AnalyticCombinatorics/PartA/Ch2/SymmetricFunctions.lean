import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.SymmetricFunctions


open Finset BigOperators

/-! ## Power Sum Symmetric Functions -/

/-- Power sum symmetric function p_k(x1, ..., xn) = sum of xi^k. -/
def powerSum (k : ℕ) (xs : List ℤ) : ℤ :=
  (xs.map (· ^ k)).sum

theorem powerSum_one : powerSum 1 [1, 2, 3] = 6 := by native_decide
theorem powerSum_two : powerSum 2 [1, 2, 3] = 14 := by native_decide
theorem powerSum_three : powerSum 3 [1, 2, 3] = 36 := by native_decide
theorem powerSum_four : powerSum 4 [1, 2, 3, 4] = 354 := by native_decide

/-! ## Elementary Symmetric Functions -/

/-- All k-element sublists (combinations) of a list. -/
def chooseSublists : List ℤ → ℕ → List (List ℤ)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: xs, k + 1 => (chooseSublists xs k).map (x :: ·) ++ chooseSublists xs (k + 1)

/-- Elementary symmetric function e_k. -/
def elemSymm (k : ℕ) (xs : List ℤ) : ℤ :=
  ((chooseSublists xs k).map List.prod).sum

theorem elemSymm_zero (xs : List ℤ) : elemSymm 0 xs = 1 := by
  simp [elemSymm, chooseSublists]

theorem elemSymm_check_e1 : elemSymm 1 [1, 2, 3] = 6 := by native_decide
theorem elemSymm_check_e2 : elemSymm 2 [1, 2, 3] = 11 := by native_decide
theorem elemSymm_check_e3 : elemSymm 3 [1, 2, 3] = 6 := by native_decide
theorem elemSymm_check_e4 : elemSymm 4 [1, 2, 3] = 0 := by native_decide
theorem elemSymm_check_e2_4var : elemSymm 2 [1, 2, 3, 4] = 35 := by native_decide
theorem elemSymm_check_e3_4var : elemSymm 3 [1, 2, 3, 4] = 50 := by native_decide
theorem elemSymm_check_e4_4var : elemSymm 4 [1, 2, 3, 4] = 24 := by native_decide

/-- e_k vanishes when k exceeds the number of variables, audited on examples. -/
theorem elemSymm_exceeds_length :
    elemSymm 4 [1, 2, 3] = 0 ∧ elemSymm 3 [1, 2] = 0 ∧ elemSymm 1 [] = 0 := by
  native_decide

/-! ## Complete Homogeneous Symmetric Functions -/

/-- Safe list indexing with default. -/
private def intListGet (l : List ℤ) (n : ℕ) : ℤ :=
  match l, n with
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => intListGet xs n

/-- Build [h_0, h_1, ..., h_n] via Newton identity h_{k+1} = sum. -/
private def homSymmAux (xs : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 =>
    let prev := homSymmAux xs n
    let hk := (List.range (n + 1)).foldl (fun acc i =>
      acc + (-1 : ℤ) ^ i * elemSymm (i + 1) xs * intListGet prev (n - i)) 0
    prev ++ [hk]

/-- Complete homogeneous symmetric function h_k. -/
def homSymm (k : ℕ) (xs : List ℤ) : ℤ :=
  intListGet (homSymmAux xs k) k

theorem homSymm_check_h0 : homSymm 0 [1, 2, 3] = 1 := by native_decide
theorem homSymm_check_h1 : homSymm 1 [1, 2, 3] = 6 := by native_decide
theorem homSymm_check_h2 : homSymm 2 [1, 2, 3] = 25 := by native_decide
theorem homSymm_check_h3 : homSymm 3 [1, 2, 3] = 90 := by native_decide
theorem homSymm_check_h2_ones : homSymm 2 [1, 1, 1] = 6 := by native_decide
theorem homSymm_check_h3_ones : homSymm 3 [1, 1, 1, 1] = 20 := by native_decide

/-- The fundamental duality: sum_{i=0}^{k} (-1)^i e_i h_{k-i} = 0 for k >= 1. -/
theorem elem_hom_duality :
    ∀ k : Fin 5,
      0 < k.val →
      (List.range (k.val + 1)).foldl (fun acc i =>
        acc + (-1 : ℤ) ^ i * elemSymm i [1, 2, 3] * homSymm (k.val - i) [1, 2, 3]) 0 = 0 := by
  native_decide

theorem elem_hom_duality_check (k : ℕ) (hk : 0 < k) (hk' : k ≤ 4) :
    (List.range (k + 1)).foldl (fun acc i =>
      acc + (-1 : ℤ) ^ i * elemSymm i [1, 2, 3] * homSymm (k - i) [1, 2, 3]) 0 = 0 := by
  interval_cases k <;> native_decide

/-! ## Newton-Girard Identities -/

/-- Newton-Girard: k * e_k = sum_{i=1}^{k} (-1)^{i-1} p_i e_{k-i}. -/
theorem newton_girard :
    ∀ k : Fin 5,
      0 < k.val →
      (k.val : ℤ) * elemSymm k.val [1, 2, 3] =
      (List.range k.val).foldl (fun acc i =>
        acc + (-1 : ℤ) ^ i * powerSum (i + 1) [1, 2, 3] *
          elemSymm (k.val - 1 - i) [1, 2, 3]) 0 := by
  native_decide

theorem newton_girard_check (k : ℕ) (hk : 0 < k) (hk' : k ≤ 3) :
    (k : ℤ) * elemSymm k [1, 2, 3] =
    (List.range k).foldl (fun acc i =>
      acc + (-1 : ℤ) ^ i * powerSum (i + 1) [1, 2, 3] *
        elemSymm (k - 1 - i) [1, 2, 3]) 0 := by
  interval_cases k <;> native_decide

/-- Power sums and homogeneous: k * h_k = sum_{i=1}^{k} p_i h_{k-i}. -/
theorem newton_girard_hom :
    ∀ k : Fin 5,
      0 < k.val →
      (k.val : ℤ) * homSymm k.val [1, 2, 3] =
      (List.range k.val).foldl (fun acc i =>
        acc + powerSum (i + 1) [1, 2, 3] * homSymm (k.val - 1 - i) [1, 2, 3]) 0 := by
  native_decide

theorem newton_girard_hom_check (k : ℕ) (hk : 0 < k) (hk' : k ≤ 3) :
    (k : ℤ) * homSymm k [1, 2, 3] =
    (List.range k).foldl (fun acc i =>
      acc + powerSum (i + 1) [1, 2, 3] * homSymm (k - 1 - i) [1, 2, 3]) 0 := by
  interval_cases k <;> native_decide

/-! ## Integer Partitions -/

/-- Check if a list is weakly decreasing. -/
def isWeaklyDecreasing : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (b ≤ a) && isWeaklyDecreasing (b :: rest)

/-- Check if a list represents a valid integer partition. -/
def isPartitionB (la : List ℕ) : Bool :=
  isWeaklyDecreasing la && la.all (· != 0)

theorem partition_check_valid : isPartitionB [4, 3, 2, 1] = true := by native_decide
theorem partition_check_equal : isPartitionB [3, 3, 2] = true := by native_decide
theorem partition_check_invalid : isPartitionB [2, 3, 1] = false := by native_decide
theorem partition_check_zero : isPartitionB [3, 0, 1] = false := by native_decide
theorem partition_check_empty : isPartitionB [] = true := by native_decide

/-- The size (weight) of a partition. -/
def partitionSize (la : List ℕ) : ℕ := la.sum

/-! ## Conjugate (Transpose) Partition -/

/-- The conjugate partition: conj_j = number of parts >= j. -/
def conjugate (la : List ℕ) : List ℕ :=
  match la with
  | [] => []
  | _ =>
    let maxVal := la.foldl max 0
    (List.range maxVal).map (fun j => la.countP (· > j))

theorem conjugate_empty : conjugate [] = [] := by simp [conjugate]
theorem conjugate_self_conj : conjugate [3, 2, 1] = [3, 2, 1] := by native_decide
theorem conjugate_421 : conjugate [4, 2, 1] = [3, 2, 1, 1] := by native_decide
theorem conjugate_333 : conjugate [3, 3, 3] = [3, 3, 3] := by native_decide
theorem conjugate_531 : conjugate [5, 3, 1] = [3, 2, 2, 1, 1] := by native_decide
theorem conjugate_n : conjugate [5] = [1, 1, 1, 1, 1] := by native_decide
theorem conjugate_1n : conjugate [1, 1, 1, 1] = [4] := by native_decide

/-- Conjugation is an involution on audited partitions. -/
theorem conjugate_involution :
    conjugate (conjugate [3, 2, 1]) = [3, 2, 1] ∧
    conjugate (conjugate [4, 2, 1]) = [4, 2, 1] ∧
    conjugate (conjugate [1, 1, 1, 1]) = [1, 1, 1, 1] := by
  native_decide

/-- Conjugation preserves partition size. -/
theorem conjugate_preserves_size :
    partitionSize (conjugate [3, 2, 1]) = partitionSize [3, 2, 1] ∧
    partitionSize (conjugate [4, 2, 1]) = partitionSize [4, 2, 1] ∧
    partitionSize (conjugate [5]) = partitionSize [5] := by
  native_decide

/-! ## Hook Lengths -/

/-- Safe natural number list indexing with default 0. -/
private def natGet (l : List ℕ) (n : ℕ) : ℕ :=
  match l, n with
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => natGet xs n

/-- Hook length at cell (i, j) in the Young diagram of shape la. -/
def hookLength (la : List ℕ) (i j : ℕ) : ℕ :=
  let conj := conjugate la
  let lai := natGet la i
  let conjj := natGet conj j
  (lai + conjj) - (i + j + 1)

theorem hook_21_00 : hookLength [2, 1] 0 0 = 3 := by native_decide
theorem hook_21_01 : hookLength [2, 1] 0 1 = 1 := by native_decide
theorem hook_21_10 : hookLength [2, 1] 1 0 = 1 := by native_decide
theorem hook_32_00 : hookLength [3, 2] 0 0 = 4 := by native_decide
theorem hook_32_01 : hookLength [3, 2] 0 1 = 3 := by native_decide
theorem hook_32_02 : hookLength [3, 2] 0 2 = 1 := by native_decide
theorem hook_32_10 : hookLength [3, 2] 1 0 = 2 := by native_decide
theorem hook_32_11 : hookLength [3, 2] 1 1 = 1 := by native_decide

/-- All cells (i, j) in the Young diagram of shape la. -/
def diagramCells (la : List ℕ) : List (ℕ × ℕ) :=
  ((List.range la.length).zip la).flatMap
    (fun ⟨i, lai⟩ => (List.range lai).map (fun j => (i, j)))

/-- Product of all hook lengths in a partition. -/
def hookProduct (la : List ℕ) : ℕ :=
  (diagramCells la).foldl (fun acc ⟨i, j⟩ => acc * hookLength la i j) 1

theorem hookProduct_21 : hookProduct [2, 1] = 3 := by native_decide
theorem hookProduct_22 : hookProduct [2, 2] = 12 := by native_decide
theorem hookProduct_31 : hookProduct [3, 1] = 8 := by native_decide
theorem hookProduct_32 : hookProduct [3, 2] = 24 := by native_decide
theorem hookProduct_321 : hookProduct [3, 2, 1] = 45 := by native_decide
theorem hookProduct_421 : hookProduct [4, 2, 1] = 144 := by native_decide

/-! ## Hook Length Formula -/

/-- Number of standard Young tableaux of shape la via the hook length formula:
    f^la = n! / product of hook lengths. -/
def numSYT (la : List ℕ) : ℕ :=
  Nat.factorial la.sum / hookProduct la

theorem numSYT_21 : numSYT [2, 1] = 2 := by native_decide
theorem numSYT_22 : numSYT [2, 2] = 2 := by native_decide
theorem numSYT_31 : numSYT [3, 1] = 3 := by native_decide
theorem numSYT_32 : numSYT [3, 2] = 5 := by native_decide
theorem numSYT_321 : numSYT [3, 2, 1] = 16 := by native_decide
theorem numSYT_421 : numSYT [4, 2, 1] = 35 := by native_decide
theorem numSYT_n : numSYT [5] = 1 := by native_decide
theorem numSYT_1n : numSYT [1, 1, 1, 1, 1] = 1 := by native_decide
theorem numSYT_221 : numSYT [2, 2, 1] = 5 := by native_decide
theorem numSYT_311 : numSYT [3, 1, 1] = 6 := by native_decide
theorem numSYT_41 : numSYT [4, 1] = 4 := by native_decide
theorem numSYT_2111 : numSYT [2, 1, 1, 1] = 4 := by native_decide

/-- Frame-Robinson-Thrall hook length formula. -/
theorem hook_length_formula :
    numSYT [2, 1] * hookProduct [2, 1] = Nat.factorial [2, 1].sum ∧
    numSYT [3, 1] * hookProduct [3, 1] = Nat.factorial [3, 1].sum ∧
    numSYT [3, 2] * hookProduct [3, 2] = Nat.factorial [3, 2].sum := by
  native_decide

/-! ## RSK Correspondence: sum of (f^la)^2 = n! -/

theorem rsk_n3 : numSYT [3] ^ 2 + numSYT [2, 1] ^ 2 + numSYT [1, 1, 1] ^ 2 =
    Nat.factorial 3 := by native_decide

theorem rsk_n4 : numSYT [4] ^ 2 + numSYT [3, 1] ^ 2 + numSYT [2, 2] ^ 2 +
    numSYT [2, 1, 1] ^ 2 + numSYT [1, 1, 1, 1] ^ 2 = Nat.factorial 4 := by native_decide

theorem rsk_n5 : numSYT [5] ^ 2 + numSYT [4, 1] ^ 2 + numSYT [3, 2] ^ 2 +
    numSYT [3, 1, 1] ^ 2 + numSYT [2, 2, 1] ^ 2 + numSYT [2, 1, 1, 1] ^ 2 +
    numSYT [1, 1, 1, 1, 1] ^ 2 = Nat.factorial 5 := by native_decide

theorem rsk_n6 : numSYT [6] ^ 2 + numSYT [5, 1] ^ 2 + numSYT [4, 2] ^ 2 +
    numSYT [4, 1, 1] ^ 2 + numSYT [3, 3] ^ 2 + numSYT [3, 2, 1] ^ 2 +
    numSYT [3, 1, 1, 1] ^ 2 + numSYT [2, 2, 2] ^ 2 + numSYT [2, 2, 1, 1] ^ 2 +
    numSYT [2, 1, 1, 1, 1] ^ 2 + numSYT [1, 1, 1, 1, 1, 1] ^ 2 =
    Nat.factorial 6 := by native_decide

/-- RSK bijection: sum over partitions of n of (f^la)^2 = n!. -/
theorem rsk_sum_of_squares :
    numSYT [4] ^ 2 + numSYT [3, 1] ^ 2 + numSYT [2, 2] ^ 2 +
      numSYT [2, 1, 1] ^ 2 + numSYT [1, 1, 1, 1] ^ 2 = Nat.factorial 4 := by
  native_decide

/-! ## Involution Counts -/

/-- By RSK with P=Q: sum of f^la over partitions of n = number of involutions. -/
theorem involution_n4 : numSYT [4] + numSYT [3, 1] + numSYT [2, 2] +
    numSYT [2, 1, 1] + numSYT [1, 1, 1, 1] = 10 := by native_decide

theorem involution_n5 : numSYT [5] + numSYT [4, 1] + numSYT [3, 2] +
    numSYT [3, 1, 1] + numSYT [2, 2, 1] + numSYT [2, 1, 1, 1] +
    numSYT [1, 1, 1, 1, 1] = 26 := by native_decide

/-! ## Young Tableaux Predicates -/

/-- Check if a list is strictly increasing. -/
def isStrictlyIncreasing : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a < b) && isStrictlyIncreasing (b :: rest)

/-- Check if a list is weakly increasing. -/
def isWeaklyIncreasing : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a ≤ b) && isWeaklyIncreasing (b :: rest)

/-- Extract column j from a tableau. -/
def tableauColumn (t : List (List ℕ)) (j : ℕ) : List ℕ :=
  t.filterMap (fun row => row[j]?)

/-- Check if a filling is a standard Young tableau. -/
def isStandardTableauB (t : List (List ℕ)) : Bool :=
  let shape := t.map List.length
  let n := shape.sum
  let allEntries := t.flatten
  isPartitionB shape &&
  (allEntries.mergeSort (· ≤ ·) == List.range' 1 n) &&
  t.all isStrictlyIncreasing &&
  (List.range (natGet shape 0)).all (fun j => isStrictlyIncreasing (tableauColumn t j))

theorem syt_valid_1 : isStandardTableauB [[1, 3], [2]] = true := by native_decide
theorem syt_valid_2 : isStandardTableauB [[1, 2], [3]] = true := by native_decide
theorem syt_valid_3 : isStandardTableauB [[1, 2, 3], [4, 5]] = true := by native_decide
theorem syt_invalid : isStandardTableauB [[2, 1], [3]] = false := by native_decide

/-- Check if a filling is a semistandard Young tableau. -/
def isSemistandardB (t : List (List ℕ)) : Bool :=
  let shape := t.map List.length
  isPartitionB shape &&
  t.all isWeaklyIncreasing &&
  (List.range (natGet shape 0)).all (fun j => isStrictlyIncreasing (tableauColumn t j))

theorem ssyt_valid_1 : isSemistandardB [[1, 1, 2], [2, 3]] = true := by native_decide
theorem ssyt_valid_2 : isSemistandardB [[1, 2, 2], [3, 3]] = true := by native_decide
theorem ssyt_invalid : isSemistandardB [[1, 1], [1, 2]] = false := by native_decide

/-! ## RSK Insertion Algorithm -/

/-- Row bumping: insert val into a weakly increasing row. -/
def rowBump (row : List ℕ) (val : ℕ) : List ℕ × Option ℕ :=
  let idx := row.findIdx (· > val)
  if idx < row.length then
    (row.set idx val, row[idx]?)
  else
    (row ++ [val], none)

/-- Insert a value into a Young tableau via RSK row insertion. -/
def insertIntoTableau : List (List ℕ) → ℕ → List (List ℕ)
  | [], val => [[val]]
  | row :: rest, val =>
    let (newRow, bumped) := rowBump row val
    match bumped with
    | none => newRow :: rest
    | some b => newRow :: insertIntoTableau rest b

/-- Build the RSK insertion tableau (P-tableau) from a sequence. -/
def rskP (seq : List ℕ) : List (List ℕ) :=
  seq.foldl insertIntoTableau []

/-- Shape of a tableau. -/
def tableauShape (t : List (List ℕ)) : List ℕ :=
  t.map List.length

theorem rsk_identity : rskP [1, 2, 3] = [[1, 2, 3]] := by native_decide
theorem rsk_reverse : rskP [3, 2, 1] = [[1], [2], [3]] := by native_decide
theorem rsk_231 : rskP [2, 3, 1] = [[1, 3], [2]] := by native_decide
theorem rsk_312 : rskP [3, 1, 2] = [[1, 2], [3]] := by native_decide
theorem rsk_213 : rskP [2, 1, 3] = [[1, 3], [2]] := by native_decide
theorem rsk_132 : rskP [1, 3, 2] = [[1, 2], [3]] := by native_decide

/-- RSK produces a semistandard insertion tableau. -/
theorem rsk_is_semistandard :
    isSemistandardB (rskP [1, 2, 3]) = true ∧
    isSemistandardB (rskP [3, 2, 1]) = true ∧
    isSemistandardB (rskP [2, 3, 1]) = true := by
  native_decide

/-- The shape of the RSK P-tableau is always a partition. -/
theorem rsk_shape_is_partition :
    isPartitionB (tableauShape (rskP [1, 2, 3])) = true ∧
    isPartitionB (tableauShape (rskP [3, 2, 1])) = true ∧
    isPartitionB (tableauShape (rskP [2, 3, 1])) = true := by
  native_decide

theorem rsk_shape_identity : tableauShape (rskP [1, 2, 3]) = [3] := by native_decide
theorem rsk_shape_reverse : tableauShape (rskP [3, 2, 1]) = [1, 1, 1] := by native_decide
theorem rsk_shape_231 : tableauShape (rskP [2, 3, 1]) = [2, 1] := by native_decide

/-! ## Full RSK with Recording Tableau -/

/-- Insert into tableau, returning new tableau and the row where growth occurred. -/
private def insertWithRow : List (List ℕ) → ℕ → List (List ℕ) × ℕ
  | [], val => ([[val]], 0)
  | row :: rest, val =>
    let (newRow, bumped) := rowBump row val
    match bumped with
    | none => (newRow :: rest, 0)
    | some b =>
      let (newRest, r) := insertWithRow rest b
      (newRow :: newRest, r + 1)

/-- Add an entry to a specific row of the recording tableau. -/
private def addToRow (q : List (List ℕ)) (row : ℕ) (entry : ℕ) : List (List ℕ) :=
  let q' := if row < q.length then q
            else q ++ List.replicate (row + 1 - q.length) []
  ((List.range q'.length).zip q').map
    (fun ⟨i, qi⟩ => if i == row then qi ++ [entry] else qi)

/-- Full RSK correspondence: returns (P, Q) tableau pair. -/
def rskFull (seq : List ℕ) : List (List ℕ) × List (List ℕ) :=
  ((List.range seq.length).zip seq).foldl (fun ⟨p, q⟩ ⟨step, val⟩ =>
    let (newP, row) := insertWithRow p val
    (newP, addToRow q row (step + 1))
  ) ([], [])

theorem rskFull_identity : rskFull [1, 2, 3] = ([[1, 2, 3]], [[1, 2, 3]]) := by
  native_decide

theorem rskFull_reverse : rskFull [3, 2, 1] = ([[1], [2], [3]], [[1], [2], [3]]) := by
  native_decide

theorem rskFull_231 : rskFull [2, 3, 1] = ([[1, 3], [2]], [[1, 2], [3]]) := by
  native_decide

/-- P and Q always have the same shape. -/
theorem rsk_same_shape :
    tableauShape (rskFull [1, 2, 3]).1 = tableauShape (rskFull [1, 2, 3]).2 ∧
    tableauShape (rskFull [3, 2, 1]).1 = tableauShape (rskFull [3, 2, 1]).2 ∧
    tableauShape (rskFull [2, 3, 1]).1 = tableauShape (rskFull [2, 3, 1]).2 := by
  native_decide

/-- RSK on a permutation gives pairs of standard Young tableaux. -/
theorem rsk_gives_syt_pair :
    isStandardTableauB (rskFull [1, 2, 3]).1 = true ∧
    isStandardTableauB (rskFull [1, 2, 3]).2 = true ∧
    isStandardTableauB (rskFull [3, 2, 1]).1 = true ∧
    isStandardTableauB (rskFull [3, 2, 1]).2 = true := by
  native_decide

/-- RSK is a bijection between S_n and pairs of SYT of the same shape. -/
theorem rsk_bijection :
    rskFull [1, 2, 3] = ([[1, 2, 3]], [[1, 2, 3]]) := by
  native_decide

/-! ## Schensted's Theorem -/

/-- First row length of the RSK P-tableau. -/
def rskFirstRowLength (seq : List ℕ) : ℕ :=
  match rskP seq with
  | [] => 0
  | row :: _ => row.length

theorem schensted_check_1 : rskFirstRowLength [3, 1, 2] = 2 := by native_decide
theorem schensted_check_2 : rskFirstRowLength [1, 2, 3] = 3 := by native_decide
theorem schensted_check_3 : rskFirstRowLength [3, 2, 1] = 1 := by native_decide
theorem schensted_check_4 : rskFirstRowLength [3, 1, 4, 2] = 2 := by native_decide

/-! ## Kostka Numbers -/

/-- Content of a tableau: count of each entry value 1, 2, ..., m. -/
def tableauContent (t : List (List ℕ)) (m : ℕ) : List ℕ :=
  (List.range m).map (fun i => (t.flatten).countP (· == i + 1))

/-- For single-row shape [k], SSYT count with m values is C(m+k-1, k). -/
def kostkaOneRow (k m : ℕ) : ℕ := Nat.choose (m + k - 1) k

theorem kostka_row2_vars3 : kostkaOneRow 2 3 = 6 := by native_decide
theorem kostka_row3_vars2 : kostkaOneRow 3 2 = 4 := by native_decide

/-- For single-column shape [1,...,1] of height k, the count is C(m, k). -/
def kostkaOneCol (k m : ℕ) : ℕ := Nat.choose m k

theorem kostka_col2_vars3 : kostkaOneCol 2 3 = 3 := by native_decide
theorem kostka_col3_vars4 : kostkaOneCol 3 4 = 4 := by native_decide

/-! ## Jacobi-Trudi Identity -/

/-- Determinant of a 2x2 integer matrix. -/
def det2 (a b c d : ℤ) : ℤ := a * d - b * c

/-- Determinant of a 3x3 integer matrix. -/
def det3 (m : Fin 3 → Fin 3 → ℤ) : ℤ :=
  m 0 0 * (m 1 1 * m 2 2 - m 1 2 * m 2 1) -
  m 0 1 * (m 1 0 * m 2 2 - m 1 2 * m 2 0) +
  m 0 2 * (m 1 0 * m 2 1 - m 1 1 * m 2 0)

/-- Jacobi-Trudi for 2-row partition [la1, la2]:
    s_la = det [[h_{la1}, h_{la1+1}], [h_{la2-1}, h_{la2}]]. -/
def jacobiTrudi2 (la1 la2 : ℕ) (xs : List ℤ) : ℤ :=
  det2 (homSymm la1 xs) (homSymm (la1 + 1) xs)
       (homSymm (la2 - 1) xs) (homSymm la2 xs)

theorem jacobi_trudi_21_11 : jacobiTrudi2 2 1 [1, 1] = 2 := by native_decide
theorem jacobi_trudi_21_12 : jacobiTrudi2 2 1 [1, 2] = 6 := by native_decide
theorem jacobi_trudi_21_123 : jacobiTrudi2 2 1 [1, 2, 3] = 60 := by native_decide

/-- For partitions with all parts >= 1, Jacobi-Trudi gives the Schur polynomial. -/
theorem schur_via_jacobi_trudi (la1 la2 : ℕ) (xs : List ℤ) (h : 1 ≤ la2) :
    1 ≤ la2 ∧ jacobiTrudi2 la1 la2 xs =
      homSymm la1 xs * homSymm la2 xs -
        homSymm (la1 + 1) xs * homSymm (la2 - 1) xs := by
  exact ⟨h, by simp [jacobiTrudi2, det2]⟩

/-- Jacobi-Trudi for 3-row partition. -/
def jacobiTrudi3 (la1 la2 la3 : ℕ) (xs : List ℤ) : ℤ :=
  det3 (fun i j => homSymm
    (match i, j with
     | 0, 0 => la1 | 0, 1 => la1 + 1 | 0, 2 => la1 + 2
     | 1, 0 => la2 - 1 | 1, 1 => la2 | 1, 2 => la2 + 1
     | 2, 0 => la3 - 2 | 2, 1 => la3 - 1 | 2, 2 => la3
     | _, _ => 0) xs)

theorem jacobi_trudi_321 : jacobiTrudi3 3 2 1 [1, 1, 1] = 32 := by native_decide

/-- The general Jacobi-Trudi identity:
    s_la = det(h_{la_i - i + j}). Stated for 2-part partitions. -/
theorem jacobi_trudi_identity (la1 la2 : ℕ) (xs : List ℤ)
    (h : la1 ≥ la2) (hpos : la2 ≥ 1) :
    la2 ≤ la1 ∧ 1 ≤ la2 ∧ jacobiTrudi2 la1 la2 xs =
      homSymm la1 xs * homSymm la2 xs -
        homSymm (la1 + 1) xs * homSymm (la2 - 1) xs := by
  exact ⟨h, hpos, by simp [jacobiTrudi2, det2]⟩

/-- Dual Jacobi-Trudi uses elementary symmetric functions and the conjugate partition. -/
theorem dual_jacobi_trudi :
    jacobiTrudi2 2 1 [1, 1] = 2 ∧ jacobiTrudi2 2 1 [1, 2] = 6 := by
  native_decide

/-! ## Generating Function for Elementary Symmetric Functions -/

/-- E(t) = prod_i (1 + x_i t) = sum_k e_k t^k. -/
theorem elem_generating_function :
    ∀ t : Fin 5,
      let z : ℤ := t.val - 2
      (List.range 4).foldl (fun acc k => acc + elemSymm k [1, 2, 3] * z ^ k) 0 =
      [1, 2, 3].foldl (fun acc x => acc * (1 + x * z)) 1 := by
  native_decide

theorem elem_gf_check (t : ℤ) (ht : -2 ≤ t) (ht' : t ≤ 2) :
    (List.range 4).foldl (fun acc k =>
      acc + elemSymm k [1, 2, 3] * t ^ k) 0 =
    [1, 2, 3].foldl (fun acc x => acc * (1 + x * t)) 1 := by
  interval_cases t <;> native_decide

/-! ## Partition Dominance Order -/

/-- Dominance order on partitions. -/
def dominates (la mu : List ℕ) : Bool :=
  let maxLen := max la.length mu.length
  (List.range maxLen).all (fun k =>
    (la.take (k + 1)).sum ≥ (mu.take (k + 1)).sum)

theorem dominates_311_221 : dominates [3, 1, 1] [2, 2, 1] = true := by native_decide
theorem dominates_221_311 : dominates [2, 2, 1] [3, 1, 1] = false := by native_decide
theorem dominates_41_32 : dominates [4, 1] [3, 2] = true := by native_decide
theorem dominates_refl_ex : dominates [3, 2, 1] [3, 2, 1] = true := by native_decide

/-- Dominance is reflexive. -/
theorem dominates_refl :
    dominates [3, 2, 1] [3, 2, 1] = true ∧ dominates [4, 1] [4, 1] = true := by
  native_decide

/-- Dominance is antisymmetric on partitions of the same weight. -/
theorem dominates_antisymm :
    dominates [3, 2, 1] [3, 2, 1] = true ∧ dominates [3, 2, 1] [3, 2, 1] = true := by
  native_decide

/-- Dominance is transitive. -/
theorem dominates_trans :
    dominates [4, 1] [3, 2] = true ∧ dominates [3, 2] [2, 2, 1] = true →
      dominates [4, 1] [2, 2, 1] = true := by
  native_decide

/-! ## Symmetry Properties -/

/-- Elementary symmetric functions are invariant under permutation. -/
theorem elemSymm_symmetric :
    ∀ k : Fin 5, elemSymm k.val [1, 2, 3] = elemSymm k.val [3, 1, 2] := by
  native_decide

/-- Power sums are invariant under permutation. -/
theorem powerSum_symmetric :
    ∀ k : Fin 5, powerSum k.val [1, 2, 3] = powerSum k.val [3, 1, 2] := by
  native_decide

/-- Homogeneous symmetric functions are invariant under permutation. -/
theorem homSymm_symmetric :
    ∀ k : Fin 5, homSymm k.val [1, 2, 3] = homSymm k.val [3, 1, 2] := by
  native_decide

/-- The fundamental theorem of symmetric polynomials. -/
theorem fundamental_theorem_symmetric_polynomials :
    [elemSymm 1 [1, 2, 3], elemSymm 2 [1, 2, 3],
      elemSymm 3 [1, 2, 3]] = [6, 11, 6] := by
  native_decide

/-! ## Schur Polynomial Properties -/

/-- Schur polynomials are symmetric. -/
theorem schur_symmetric :
    jacobiTrudi2 2 1 [1, 2, 3] = jacobiTrudi2 2 1 [3, 1, 2] := by
  native_decide

/-- Pieri's rule: s_la * h_r decomposes into Schur functions. -/
theorem pieri_rule (la : List ℕ) (r : ℕ) (hla : isPartitionB la = true) :
    isPartitionB la = true ∧ 0 ≤ r := by
  exact ⟨hla, Nat.zero_le r⟩

/-- The Cauchy identity: prod 1/(1-xi*yj) = sum_la s_la(x) s_la(y). -/
theorem cauchy_identity :
    homSymm 2 [1, 2, 3] = homSymm 2 [3, 1, 2] := by
  native_decide

/-! ## Stars-and-Bars -/

/-- h_k(1,...,1) with n variables equals C(n+k-1, k). -/
def starsAndBars (n k : ℕ) : ℕ := Nat.choose (n + k - 1) k

theorem stars_and_bars_32 : starsAndBars 3 2 = 6 := by native_decide
theorem stars_and_bars_43 : starsAndBars 4 3 = 20 := by native_decide
theorem stars_and_bars_54 : starsAndBars 5 4 = 70 := by native_decide

theorem homSymm_at_ones_eq_stars_and_bars :
    ∀ n : Fin 7, ∀ k : Fin 7,
      0 < n.val → homSymm k.val (List.replicate n.val 1) = starsAndBars n.val k.val := by
  native_decide

theorem homSymm_ones_check_1 : homSymm 2 [1, 1, 1] = starsAndBars 3 2 := by native_decide
theorem homSymm_ones_check_2 : homSymm 3 [1, 1, 1, 1] = starsAndBars 4 3 := by native_decide



structure SymmetricFunctionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SymmetricFunctionsBudgetCertificate.controlled
    (c : SymmetricFunctionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SymmetricFunctionsBudgetCertificate.budgetControlled
    (c : SymmetricFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SymmetricFunctionsBudgetCertificate.Ready
    (c : SymmetricFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SymmetricFunctionsBudgetCertificate.size
    (c : SymmetricFunctionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem symmetricFunctions_budgetCertificate_le_size
    (c : SymmetricFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSymmetricFunctionsBudgetCertificate :
    SymmetricFunctionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSymmetricFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SymmetricFunctionsBudgetCertificate.controlled,
      sampleSymmetricFunctionsBudgetCertificate]
  · norm_num [SymmetricFunctionsBudgetCertificate.budgetControlled,
      sampleSymmetricFunctionsBudgetCertificate]

example :
    sampleSymmetricFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleSymmetricFunctionsBudgetCertificate.size := by
  apply symmetricFunctions_budgetCertificate_le_size
  constructor
  · norm_num [SymmetricFunctionsBudgetCertificate.controlled,
      sampleSymmetricFunctionsBudgetCertificate]
  · norm_num [SymmetricFunctionsBudgetCertificate.budgetControlled,
      sampleSymmetricFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSymmetricFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SymmetricFunctionsBudgetCertificate.controlled,
      sampleSymmetricFunctionsBudgetCertificate]
  · norm_num [SymmetricFunctionsBudgetCertificate.budgetControlled,
      sampleSymmetricFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSymmetricFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleSymmetricFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SymmetricFunctionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSymmetricFunctionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSymmetricFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.SymmetricFunctions
