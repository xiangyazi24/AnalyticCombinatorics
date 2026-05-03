import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace RecordValues

/-! # Record Values in Random Permutations

A left-to-right maximum (record) at position k in a permutation σ means
σ(k) > σ(j) for all j < k. The expected number of records in a random
permutation of [n] equals the harmonic number H_n = Σ_{k=1}^n 1/k.

Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter 9.
-/

section Computational

def isRecord (σ : List ℕ) (k : ℕ) : Bool :=
  if hk : k < σ.length then
    (List.range k).all fun j =>
      if hj : j < σ.length then
        Nat.blt σ[j] σ[k]
      else
        true
  else
    false

def countRecords (σ : List ℕ) : ℕ :=
  (List.range σ.length).countP fun k => isRecord σ k

def permsOfN (n : ℕ) : List (List ℕ) :=
  ((List.range n).map (· + 1)).permutations

def countPermsWithKRecords (n k : ℕ) : ℕ :=
  (permsOfN n).countP fun σ => countRecords σ == k

def totalRecords (n : ℕ) : ℕ :=
  ((permsOfN n).map countRecords).sum

end Computational

section Verification

example : isRecord [3, 1, 4, 2] 0 = true := by native_decide
example : isRecord [3, 1, 4, 2] 1 = false := by native_decide
example : isRecord [3, 1, 4, 2] 2 = true := by native_decide
example : isRecord [3, 1, 4, 2] 3 = false := by native_decide

example : countRecords [1, 2, 3, 4] = 4 := by native_decide
example : countRecords [4, 3, 2, 1] = 1 := by native_decide
example : countRecords [1, 4, 3, 2] = 2 := by native_decide
example : countRecords [2, 4, 1, 3] = 2 := by native_decide

example : (permsOfN 3).length = 6 := by native_decide
example : (permsOfN 4).length = 24 := by native_decide

/-- Permutations of [4] with exactly 2 records = 11 (unsigned Stirling number c(4,2)) -/
example : countPermsWithKRecords 4 2 = 11 := by native_decide

example : countPermsWithKRecords 4 1 = 6 := by native_decide
example : countPermsWithKRecords 4 3 = 6 := by native_decide
example : countPermsWithKRecords 4 4 = 1 := by native_decide

example : countPermsWithKRecords 3 1 = 2 := by native_decide
example : countPermsWithKRecords 3 2 = 3 := by native_decide
example : countPermsWithKRecords 3 3 = 1 := by native_decide

/-- Total records over all perms of [3] = 3! · H_3 = 6 · 11/6 = 11 -/
example : totalRecords 3 = 11 := by native_decide

/-- Total records over all perms of [4] = 4! · H_4 = 24 · 25/12 = 50 -/
example : totalRecords 4 = 50 := by native_decide

end Verification

section StirlingRecurrence

def stirling1Unsigned (n k : ℕ) : ℕ := countPermsWithKRecords n k

/-- Recurrence: c(n+1, k) = n · c(n, k) + c(n, k-1) -/
example : stirling1Unsigned 4 2 = 3 * stirling1Unsigned 3 2 + stirling1Unsigned 3 1 := by
  native_decide

example : stirling1Unsigned 4 3 = 3 * stirling1Unsigned 3 3 + stirling1Unsigned 3 2 := by
  native_decide

/-- Row sum: Σ_k c(n,k) = n! -/
example : stirling1Unsigned 4 1 + stirling1Unsigned 4 2 +
    stirling1Unsigned 4 3 + stirling1Unsigned 4 4 = 24 := by native_decide

/-- Rising factorial: Σ_k c(n,k) · u^k = u(u+1)···(u+n-1), verified at u=2, n=3 -/
example : stirling1Unsigned 3 1 * 2 + stirling1Unsigned 3 2 * 4 +
    stirling1Unsigned 3 3 * 8 = 2 * 3 * 4 := by native_decide

end StirlingRecurrence

section Formal

open Classical

def IsRecordAt {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) : Prop :=
  ∀ j : Fin n, j.val < k.val → σ j < σ k

noncomputable def numRecords {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun k => IsRecordAt σ k)).card

theorem first_is_record {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    IsRecordAt σ ⟨0, Nat.zero_lt_succ n⟩ := by
  intro j hj
  exact absurd hj (Nat.not_lt_zero _)

theorem has_at_least_one_record {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    0 < numRecords σ := by
  unfold numRecords
  rw [Finset.card_pos]
  exact ⟨⟨0, Nat.zero_lt_succ n⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, first_is_record σ⟩⟩

theorem identity_all_records {n : ℕ} :
    ∀ k : Fin n, IsRecordAt (Equiv.refl (Fin n)) k := by
  intro k j hj
  simp only [Equiv.refl_apply]
  exact hj

/-- Position k is a record iff σ(k) is the maximum of σ(0), ..., σ(k) -/
theorem record_iff_max_prefix {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    IsRecordAt σ k ↔ ∀ j : Fin n, j.val ≤ k.val → σ j ≤ σ k := by
  sorry

/-- Among all n! permutations, position k is a record in exactly n!/(k+1) of them.
    This is because σ(k) is the max of the first k+1 values with probability 1/(k+1). -/
theorem record_count_at_position {n : ℕ} (k : Fin n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => IsRecordAt σ k)).card * (k.val + 1) =
    Nat.factorial n := by
  sorry

/-- The expected number of records equals H_n (harmonic number).
    Equivalently: sum of records over all permutations = Σ_{k=0}^{n-1} n!/(k+1). -/
theorem total_records_harmonic {n : ℕ} :
    Finset.sum Finset.univ (fun σ : Equiv.Perm (Fin n) => numRecords σ) =
    Finset.sum (Finset.range n) (fun k => Nat.factorial n / (k + 1)) := by
  sorry

/-- The number of permutations of [n] with exactly k records equals |s(n,k)|,
    the unsigned Stirling number of the first kind. -/
theorem records_eq_stirling {n k : ℕ} :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => numRecords σ = k)).card =
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (Equiv.Perm.cycleType σ).card = k)).card := by
  sorry

end Formal

end RecordValues
