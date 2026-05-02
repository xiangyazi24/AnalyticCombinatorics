import AnalyticCombinatorics.PartA.Ch3.Parameters
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open CombinatorialClass

/-! # Ch III/IX — Multivariate Generating Functions

Bivariate generating functions mark an ordinary size variable together with
one combinatorial parameter.  This file adds small finite examples for the
existing `CombinatorialClass.bgf`, and records the Eulerian-number table for
descents in permutations.
-/

namespace MultivariateGF

/-! ## Worked `bgf` examples -/

/-- Two labelled choices, both of size `1`. -/
def twoAtomsOfSizeOne : CombinatorialClass where
  Obj := Bool
  size _ := 1
  finite_level _ := Set.finite_univ.subset (Set.subset_univ _)

instance : Fintype twoAtomsOfSizeOne.Obj := inferInstanceAs (Fintype Bool)
instance : DecidableEq twoAtomsOfSizeOne.Obj := inferInstanceAs (DecidableEq Bool)

/-- A marker parameter separating the two objects. -/
def boolMarker : Parameter twoAtomsOfSizeOne := fun b =>
  match (show Bool from b) with
  | false => 0
  | true => 1

@[simp]
theorem twoAtomsOfSizeOne_level_zero :
    twoAtomsOfSizeOne.level 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsize := (CombinatorialClass.level_mem_iff (C := twoAtomsOfSizeOne) b).mp hb
  simp [twoAtomsOfSizeOne] at hsize

@[simp]
theorem twoAtomsOfSizeOne_level_one :
    twoAtomsOfSizeOne.level 1 = Finset.univ := by
  ext b
  constructor
  · intro _hb
    exact Finset.mem_univ b
  · intro _hb
    rw [CombinatorialClass.level_mem_iff]
    simp [twoAtomsOfSizeOne]

@[simp]
theorem boolMarker_false : boolMarker false = 0 := rfl

@[simp]
theorem boolMarker_true : boolMarker true = 1 := rfl

example : twoAtomsOfSizeOne.jointCount boolMarker 1 0 = 1 := by
  rw [CombinatorialClass.jointCount, twoAtomsOfSizeOne_level_one]
  change ((Finset.univ : Finset Bool).filter
    (fun a => boolMarker a = 0)).card = 1
  native_decide

example : twoAtomsOfSizeOne.jointCount boolMarker 1 1 = 1 := by
  rw [CombinatorialClass.jointCount, twoAtomsOfSizeOne_level_one]
  change ((Finset.univ : Finset Bool).filter
    (fun a => boolMarker a = 1)).card = 1
  native_decide

example : twoAtomsOfSizeOne.jointCount boolMarker 1 2 = 0 := by
  rw [CombinatorialClass.jointCount, twoAtomsOfSizeOne_level_one]
  change ((Finset.univ : Finset Bool).filter
    (fun a => boolMarker a = 2)).card = 0
  native_decide

/-- At size `1`, the two marker values present are exactly `0` and `1`. -/
example :
    Finset.image boolMarker (twoAtomsOfSizeOne.level 1) = ({0, 1} : Finset ℕ) := by
  rw [twoAtomsOfSizeOne_level_one]
  native_decide

example : PowerSeries.coeff 0 (twoAtomsOfSizeOne.bgf boolMarker) = 0 := by
  rw [CombinatorialClass.coeff_bgf, twoAtomsOfSizeOne_level_zero]
  simp

/-! ## Eulerian numbers -/

/-- `eulerianNumber n k` is the Eulerian number `A(n,k)`, counting permutations
of `[n]` with exactly `k` descents. -/
def eulerianNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 =>
      (k + 2) * eulerianNumber n (k + 1) + (n - k) * eulerianNumber n k

@[simp]
theorem eulerianNumber_zero_zero : eulerianNumber 0 0 = 1 := rfl

@[simp]
theorem eulerianNumber_zero_succ (k : ℕ) : eulerianNumber 0 (k + 1) = 0 := rfl

@[simp]
theorem eulerianNumber_succ_zero (n : ℕ) : eulerianNumber (n + 1) 0 = 1 := rfl

@[simp]
theorem eulerianNumber_succ_succ (n k : ℕ) :
    eulerianNumber (n + 1) (k + 1) =
      (k + 2) * eulerianNumber n (k + 1) + (n - k) * eulerianNumber n k := rfl

/-- The usual recurrence away from the left boundary. -/
theorem eulerianNumber_rec {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    eulerianNumber n k =
      (k + 1) * eulerianNumber (n - 1) k +
        (n - k) * eulerianNumber (n - 1) (k - 1) := by
  cases n with
  | zero => omega
  | succ n =>
      cases k with
      | zero => omega
      | succ k =>
          simp [Nat.succ_sub_succ_eq_sub]

/-- The left boundary `A(n,0)=1` for positive rows. -/
theorem eulerianNumber_left_boundary (n : ℕ) :
    eulerianNumber (n + 1) 0 = 1 := rfl

/-- Eulerian rows vanish outside the range `0 ≤ k < n`, except for `A(0,0)`. -/
theorem eulerianNumber_eq_zero_of_ge {n k : ℕ} (hn : 0 < n) (hk : n ≤ k) :
    eulerianNumber n k = 0 := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          have hnk : n ≤ k := Nat.succ_le_succ_iff.mp hk
          have hcoef : n - k = 0 := Nat.sub_eq_zero_of_le hnk
          have hfirst : eulerianNumber n (k + 1) = 0 := by
            cases n with
            | zero => rfl
            | succ n =>
                apply ih
                · omega
                · omega
          simp [hcoef, hfirst]

/-- Sum over all possible descent counts in row `n`. -/
def eulerianRowSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), eulerianNumber n k

/-- Boolean row-symmetry checker over the finite range `0 ≤ k < n`. -/
def eulerianSymmetryCheck (n : ℕ) : Bool :=
  (List.range n).all fun k =>
    eulerianNumber n k == eulerianNumber n (n - 1 - k)

/-! ### Small Eulerian table -/

example : eulerianNumber 3 0 = 1 := by native_decide
example : eulerianNumber 3 1 = 4 := by native_decide
example : eulerianNumber 3 2 = 1 := by native_decide

example : eulerianNumber 4 0 = 1 := by native_decide
example : eulerianNumber 4 1 = 11 := by native_decide
example : eulerianNumber 4 2 = 11 := by native_decide
example : eulerianNumber 4 3 = 1 := by native_decide

/-! ### Row sums `Σₖ A(n,k)=n!`, checked for `n=0..7` -/

example : eulerianRowSum 0 = Nat.factorial 0 := by native_decide
example : eulerianRowSum 1 = Nat.factorial 1 := by native_decide
example : eulerianRowSum 2 = Nat.factorial 2 := by native_decide
example : eulerianRowSum 3 = Nat.factorial 3 := by native_decide
example : eulerianRowSum 4 = Nat.factorial 4 := by native_decide
example : eulerianRowSum 5 = Nat.factorial 5 := by native_decide
example : eulerianRowSum 6 = Nat.factorial 6 := by native_decide
example : eulerianRowSum 7 = Nat.factorial 7 := by native_decide

/-! ### Symmetry `A(n,k)=A(n,n-1-k)`, checked for `n=1..6` -/

example : eulerianSymmetryCheck 1 = true := by native_decide
example : eulerianSymmetryCheck 2 = true := by native_decide
example : eulerianSymmetryCheck 3 = true := by native_decide
example : eulerianSymmetryCheck 4 = true := by native_decide
example : eulerianSymmetryCheck 5 = true := by native_decide
example : eulerianSymmetryCheck 6 = true := by native_decide

end MultivariateGF
