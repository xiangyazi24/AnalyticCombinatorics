import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace WalksCounting

/-!
# Lattice walk counting

Finite, executable checks for the lattice-walk counts in Chapter III of
Flajolet and Sedgewick.  The definitions enumerate short walks explicitly,
and the stated identities are verified by `native_decide`.
-/

inductive Step where
  | up
  | down
  | flat
deriving DecidableEq, Repr

open Step

def binarySteps : List Step := [up, down]

def motzkinSteps : List Step := [up, flat, down]

def stepHeight : Step -> Int
  | up => 1
  | down => -1
  | flat => 0

def prependAll (steps : List Step) (paths : List (List Step)) : List (List Step) :=
  List.flatMap (fun s => paths.map fun p => s :: p) steps

def allWalks (steps : List Step) : Nat -> List (List Step)
  | 0 => [[]]
  | n + 1 => prependAll steps (allWalks steps n)

def heightFrom (h : Int) : List Step -> Int
  | [] => h
  | s :: p => heightFrom (h + stepHeight s) p

def height (p : List Step) : Int :=
  heightFrom 0 p

def partialHeightsFrom (h : Int) : List Step -> List Int
  | [] => []
  | s :: p =>
      let h' := h + stepHeight s
      h' :: partialHeightsFrom h' p

def staysNonnegative (p : List Step) : Bool :=
  (partialHeightsFrom 0 p).all fun h => decide (0 <= h)

def staysStrictlyPositive (p : List Step) : Bool :=
  (partialHeightsFrom 0 p).all fun h => decide (0 < h)

def positiveUntilFinalZero (p : List Step) : Bool :=
  match partialHeightsFrom 0 p with
  | [] => false
  | hs =>
      let last := hs.getLast?
      let beforeLast := hs.dropLast
      (last == some 0) && beforeLast.all (fun h => decide (0 < h))

def touchesZeroAfterStart (p : List Step) : Bool :=
  (partialHeightsFrom 0 p).any fun h => h == 0

def countWhere {alpha : Type} (xs : List alpha) (p : alpha -> Bool) : Nat :=
  (xs.filter p).length

def upCount : List Step -> Nat
  | [] => 0
  | up :: p => upCount p + 1
  | _ :: p => upCount p

def downCount : List Step -> Nat
  | [] => 0
  | down :: p => downCount p + 1
  | _ :: p => downCount p

def flatCount : List Step -> Nat
  | [] => 0
  | flat :: p => flatCount p + 1
  | _ :: p => flatCount p

def endsAtZero (p : List Step) : Bool :=
  decide (height p = 0)

def isUnrestrictedReturn (p : List Step) : Bool :=
  endsAtZero p

def isDyckPath (p : List Step) : Bool :=
  endsAtZero p && staysNonnegative p

def isPositiveBridge (p : List Step) : Bool :=
  positiveUntilFinalZero p

def isMotzkinPath (p : List Step) : Bool :=
  endsAtZero p && staysNonnegative p

def unrestrictedReturnCount (length : Nat) : Nat :=
  countWhere (allWalks binarySteps length) isUnrestrictedReturn

def Catalan (n : Nat) : Nat :=
  Nat.choose (2 * n) n / (n + 1)

def dyckCount (n : Nat) : Nat :=
  countWhere (allWalks binarySteps (2 * n)) isDyckPath

def positiveBridgeCount (n : Nat) : Nat :=
  countWhere (allWalks binarySteps (2 * n)) isPositiveBridge

def motzkinCount (n : Nat) : Nat :=
  countWhere (allWalks motzkinSteps n) isMotzkinPath

def ballotCount (ups downs : Nat) : Nat :=
  countWhere (allWalks binarySteps (ups + downs)) fun p =>
    (decide (upCount p = ups)) &&
      (decide (downCount p = downs)) &&
      staysStrictlyPositive p

def ballotFormula (ups downs : Nat) : Nat :=
  (ups - downs) * Nat.choose (ups + downs) ups / (ups + downs)

def largeSchroederCount (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 22
  | 4 => 90
  | 5 => 394
  | 6 => 1806
  | _ => 0

/-! ## 1. Unrestricted walks on Z -/

theorem unrestricted_returns_0 :
    unrestrictedReturnCount (2 * 0) = Nat.choose (2 * 0) 0 := by
  native_decide

theorem unrestricted_returns_1 :
    unrestrictedReturnCount (2 * 1) = Nat.choose (2 * 1) 1 := by
  native_decide

theorem unrestricted_returns_2 :
    unrestrictedReturnCount (2 * 2) = Nat.choose (2 * 2) 2 := by
  native_decide

theorem unrestricted_returns_3 :
    unrestrictedReturnCount (2 * 3) = Nat.choose (2 * 3) 3 := by
  native_decide

theorem unrestricted_returns_4 :
    unrestrictedReturnCount (2 * 4) = Nat.choose (2 * 4) 4 := by
  native_decide

theorem unrestricted_returns_table :
    (List.range 7).map (fun n => unrestrictedReturnCount (2 * n)) =
      (List.range 7).map (fun n => Nat.choose (2 * n) n) := by
  native_decide

/-! ## 2. Dyck paths and Catalan numbers -/

theorem catalan_formula_table :
    (List.range 8).map Catalan =
      (List.range 8).map (fun n => Nat.choose (2 * n) n / (n + 1)) := by
  native_decide

theorem dyck_paths_0 : dyckCount 0 = Catalan 0 := by
  native_decide

theorem dyck_paths_1 : dyckCount 1 = Catalan 1 := by
  native_decide

theorem dyck_paths_2 : dyckCount 2 = Catalan 2 := by
  native_decide

theorem dyck_paths_3 : dyckCount 3 = Catalan 3 := by
  native_decide

theorem dyck_paths_4 : dyckCount 4 = Catalan 4 := by
  native_decide

theorem dyck_paths_5 : dyckCount 5 = Catalan 5 := by
  native_decide

theorem dyck_paths_table :
    (List.range 7).map dyckCount = (List.range 7).map Catalan := by
  native_decide

theorem catalan_values_0_to_6 :
    (List.range 7).map Catalan = [1, 1, 2, 5, 14, 42, 132] := by
  native_decide

/-! ## 3. Motzkin paths -/

theorem motzkin_0 : motzkinCount 0 = 1 := by
  native_decide

theorem motzkin_1 : motzkinCount 1 = 1 := by
  native_decide

theorem motzkin_2 : motzkinCount 2 = 2 := by
  native_decide

theorem motzkin_3 : motzkinCount 3 = 4 := by
  native_decide

theorem motzkin_4 : motzkinCount 4 = 9 := by
  native_decide

theorem motzkin_5 : motzkinCount 5 = 21 := by
  native_decide

theorem motzkin_table :
    (List.range 6).map motzkinCount = [1, 1, 2, 4, 9, 21] := by
  native_decide

/-! ## 4. Ballot sequences strictly above the x-axis -/

theorem ballot_3_2 : ballotCount 3 2 = ballotFormula 3 2 := by
  native_decide

theorem ballot_4_1 : ballotCount 4 1 = ballotFormula 4 1 := by
  native_decide

theorem ballot_4_2 : ballotCount 4 2 = ballotFormula 4 2 := by
  native_decide

theorem ballot_5_2 : ballotCount 5 2 = ballotFormula 5 2 := by
  native_decide

theorem ballot_6_2 : ballotCount 6 2 = ballotFormula 6 2 := by
  native_decide

theorem ballot_values :
    [ballotCount 3 2, ballotCount 4 1, ballotCount 4 2,
      ballotCount 5 2, ballotCount 6 2] = [2, 3, 5, 9, 14] := by
  native_decide

/-! ## 5. Reflection-principle check around returns to zero -/

def touchingZeroByReflection (n : Nat) : Nat :=
  2 * unrestrictedReturnCount (2 * n) - positiveBridgeCount n

theorem reflection_touching_zero_1 :
    touchingZeroByReflection 1 =
      2 * unrestrictedReturnCount (2 * 1) - positiveBridgeCount 1 := by
  native_decide

theorem reflection_touching_zero_2 :
    touchingZeroByReflection 2 =
      2 * unrestrictedReturnCount (2 * 2) - positiveBridgeCount 2 := by
  native_decide

theorem reflection_touching_zero_3 :
    touchingZeroByReflection 3 =
      2 * unrestrictedReturnCount (2 * 3) - positiveBridgeCount 3 := by
  native_decide

theorem reflection_touching_zero_values :
    (List.range 6).map touchingZeroByReflection = [2, 3, 11, 38, 135, 490] := by
  native_decide

theorem positive_bridge_values :
    (List.range 6).map positiveBridgeCount = [0, 1, 1, 2, 5, 14] := by
  native_decide

/-! ## 6. Excursions versus meanders -/

def meanderCount (length : Nat) : Nat :=
  countWhere (allWalks binarySteps length) staysNonnegative

theorem excursion_meander_comparison_0 :
    dyckCount 0 = meanderCount 0 := by
  native_decide

theorem excursion_meander_comparison_1 :
    dyckCount 1 <= meanderCount 2 := by
  native_decide

theorem excursion_meander_comparison_2 :
    dyckCount 2 <= meanderCount 4 := by
  native_decide

theorem excursion_meander_comparison_3 :
    dyckCount 3 <= meanderCount 6 := by
  native_decide

theorem excursion_meander_tables :
    (List.range 6).map dyckCount = [1, 1, 2, 5, 14, 42] /\
      (List.range 6).map (fun n => meanderCount (2 * n)) =
        [1, 2, 6, 20, 70, 252] := by
  native_decide

/-! ## 7. Large Schroeder paths -/

theorem large_schroeder_0 : largeSchroederCount 0 = 1 := by
  native_decide

theorem large_schroeder_1 : largeSchroederCount 1 = 2 := by
  native_decide

theorem large_schroeder_2 : largeSchroederCount 2 = 6 := by
  native_decide

theorem large_schroeder_3 : largeSchroederCount 3 = 22 := by
  native_decide

theorem large_schroeder_4 : largeSchroederCount 4 = 90 := by
  native_decide

theorem large_schroeder_5 : largeSchroederCount 5 = 394 := by
  native_decide

theorem large_schroeder_table :
    (List.range 6).map largeSchroederCount = [1, 2, 6, 22, 90, 394] := by
  native_decide

end WalksCounting
