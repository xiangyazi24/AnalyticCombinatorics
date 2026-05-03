import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AsymptoticExpansionSchemes

/-!
Finite, computable models for Chapter VII asymptotic-expansion schemes.
The records encode the universal expansion shapes, while the theorems below
verify concrete coefficient prefixes, structure constants, and ratio formulae.
-/

open Finset

/-! ## 1. Simple families of trees: `T = z * phi T` -/

structure SquareRootTreeAsymptotic where
  rho : ℚ
  inverseExponentialBase : ℕ
  subexponentNum : ℤ
  subexponentDen : ℕ
  constantPositive : Bool

def simpleTreeUniversalLaw : SquareRootTreeAsymptotic where
  rho := (1 : ℚ) / 4
  inverseExponentialBase := 4
  subexponentNum := (-3 : ℤ)
  subexponentDen := 2
  constantPositive := true

def evalNatPolynomial (coeff : ℕ → ℕ) (degree x : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (degree + 1), coeff k * x ^ k

def evalNatPolynomialDerivative (coeff : ℕ → ℕ) (degree x : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (degree + 1),
    if k = 0 then 0 else k * coeff k * x ^ (k - 1)

def binaryTreePhiCoeff : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

def centralBinomial (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n

def catalanNumber (n : ℕ) : ℕ :=
  centralBinomial n / (n + 1)

def catalanSuccessiveRatio (n : ℕ) : ℚ :=
  (catalanNumber (n + 1) : ℚ) / (catalanNumber n : ℚ)

def catalanClosedSuccessiveRatio (n : ℕ) : ℚ :=
  (2 * (2 * n + 1) : ℚ) / (n + 2 : ℚ)

def catalanConvolution (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), catalanNumber i * catalanNumber (n - i)

theorem simple_tree_universal_square_root_shape :
    simpleTreeUniversalLaw.rho = (1 : ℚ) / 4 ∧
      simpleTreeUniversalLaw.inverseExponentialBase = 4 ∧
      simpleTreeUniversalLaw.subexponentNum = (-3 : ℤ) ∧
      simpleTreeUniversalLaw.subexponentDen = 2 ∧
      simpleTreeUniversalLaw.constantPositive = true := by
  native_decide

theorem binary_tree_phi_structure_constants :
    evalNatPolynomial binaryTreePhiCoeff 2 1 = 4 ∧
      evalNatPolynomialDerivative binaryTreePhiCoeff 2 1 = 4 ∧
      1 * evalNatPolynomialDerivative binaryTreePhiCoeff 2 1 =
        evalNatPolynomial binaryTreePhiCoeff 2 1 ∧
      simpleTreeUniversalLaw.rho = (1 : ℚ) / 4 := by
  native_decide

theorem catalan_closed_form_upto_ten :
    List.ofFn (fun n : Fin 11 => catalanNumber n.val) =
      [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796] := by
  native_decide

theorem catalan_convolution_equation_upto_ten :
    List.ofFn (fun n : Fin 10 => catalanNumber (n.val + 1)) =
      List.ofFn (fun n : Fin 10 => catalanConvolution n.val) := by
  native_decide

theorem catalan_successive_ratios_upto_ten :
    List.ofFn (fun n : Fin 10 => catalanSuccessiveRatio n.val) =
      List.ofFn (fun n : Fin 10 => catalanClosedSuccessiveRatio n.val) := by
  native_decide

/-! ## 2. 2-3 trees, counted by leaves -/

structure BranchingRange where
  minBranching : ℕ
  maxBranching : ℕ

def twoThreeBranchingRange : BranchingRange where
  minBranching := 2
  maxBranching := 3

def inTwoThreeBranchingRange (k : ℕ) : Bool :=
  twoThreeBranchingRange.minBranching ≤ k &&
    k ≤ twoThreeBranchingRange.maxBranching

def multinomial3 (a b c : ℕ) : ℕ :=
  Nat.factorial (a + b + c) /
    (Nat.factorial a * Nat.factorial b * Nat.factorial c)

def twoThreeTreeCountByLeaves (leaves : ℕ) : ℕ :=
  ∑ t ∈ Finset.range ((leaves - 1) / 2 + 1),
    let b := leaves - 1 - 2 * t
    let nodes := leaves + b + t
    if 1 ≤ leaves ∧ leaves = b + 2 * t + 1 then
      multinomial3 leaves b t / nodes
    else
      0

theorem two_three_branching_range_values :
    List.ofFn (fun k : Fin 6 => inTwoThreeBranchingRange k.val) =
      [false, false, true, true, false, false] := by
  native_decide

theorem two_three_trees_by_leaves_upto_twelve :
    List.ofFn (fun i : Fin 12 => twoThreeTreeCountByLeaves (i.val + 1)) =
      [1, 1, 3, 10, 38, 154, 654, 2871, 12925, 59345, 276835, 1308320] := by
  native_decide

/-! ## 3. Labelled rooted forests and Cayley counts -/

def labelledRootedCayleyCount (n : ℕ) : ℕ :=
  if n = 0 then 0 else n ^ (n - 1)

theorem labelled_rooted_cayley_counts_small :
    List.ofFn (fun i : Fin 8 => labelledRootedCayleyCount (i.val + 1)) =
      [1, 2, 9, 64, 625, 7776, 117649, 2097152] := by
  native_decide

theorem labelled_rooted_cayley_formula_small :
    List.ofFn (fun i : Fin 8 => labelledRootedCayleyCount (i.val + 1)) =
      List.ofFn (fun i : Fin 8 => (i.val + 1) ^ i.val) := by
  native_decide

/-! ## 4. Ordered factorizations -/

def properFactor (d n : ℕ) : Bool :=
  2 ≤ d && n % d = 0

def orderedFactorizationCountFuel : ℕ → ℕ → ℕ
  | 0, n => if n = 1 then 1 else 0
  | fuel + 1, n =>
      if n = 1 then
        1
      else
        ∑ d ∈ Finset.range (n + 1),
          if properFactor d n then orderedFactorizationCountFuel fuel (n / d) else 0

def orderedFactorizationCount (n : ℕ) : ℕ :=
  orderedFactorizationCountFuel n n

theorem ordered_factorizations_upto_twenty :
    List.ofFn (fun i : Fin 20 => orderedFactorizationCount (i.val + 1)) =
      [1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 8, 1, 3, 3, 8, 1, 8, 1, 8] := by
  native_decide

theorem ordered_factorization_prime_examples :
    orderedFactorizationCount 2 = 1 ∧
      orderedFactorizationCount 3 = 1 ∧
      orderedFactorizationCount 5 = 1 ∧
      orderedFactorizationCount 7 = 1 ∧
      orderedFactorizationCount 11 = 1 := by
  native_decide

/-! ## 5. Plane trees with degree constraints -/

def unaryBinaryDegreeAllowed (d : ℕ) : Bool :=
  d = 0 || d = 1 || d = 2

def fullBinaryDegreeAllowed (d : ℕ) : Bool :=
  d = 0 || d = 2

def motzkinNumber (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * k) * catalanNumber k

def unaryBinaryPlaneTreeCountByNodes (n : ℕ) : ℕ :=
  if n = 0 then 0 else motzkinNumber (n - 1)

def fullBinaryPlaneTreeCountByNodes (n : ℕ) : ℕ :=
  if n % 2 = 1 then catalanNumber ((n - 1) / 2) else 0

theorem degree_constraint_predicates_small :
    List.ofFn (fun d : Fin 5 => unaryBinaryDegreeAllowed d.val) =
        [true, true, true, false, false] ∧
      List.ofFn (fun d : Fin 5 => fullBinaryDegreeAllowed d.val) =
        [true, false, true, false, false] := by
  native_decide

theorem unary_binary_plane_trees_nodes_upto_eleven :
    List.ofFn (fun i : Fin 11 => unaryBinaryPlaneTreeCountByNodes (i.val + 1)) =
      [1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188] := by
  native_decide

theorem full_binary_plane_trees_nodes_upto_eleven :
    List.ofFn (fun i : Fin 11 => fullBinaryPlaneTreeCountByNodes (i.val + 1)) =
      [1, 0, 1, 0, 2, 0, 5, 0, 14, 0, 42] := by
  native_decide

/-! ## 6. Supercritical sequence schemas: binary words avoiding `00` -/

structure SupercriticalSequenceSchema where
  alphabetSize : ℕ
  forbiddenPatternLength : ℕ
  recurrenceOrder : ℕ

def noDoubleZeroSequenceSchema : SupercriticalSequenceSchema where
  alphabetSize := 2
  forbiddenPatternLength := 2
  recurrenceOrder := 2

def binaryWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (binaryWords n).flatMap fun w => [false :: w, true :: w]

def avoidsDoubleZero : List Bool → Bool
  | [] => true
  | [_] => true
  | false :: false :: _ => false
  | _ :: rest => avoidsDoubleZero rest

def wordsAvoidingDoubleZeroCount (n : ℕ) : ℕ :=
  ((binaryWords n).filter avoidsDoubleZero).length

def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci (n + 1) + fibonacci n

theorem no_double_zero_schema_constants :
    noDoubleZeroSequenceSchema.alphabetSize = 2 ∧
      noDoubleZeroSequenceSchema.forbiddenPatternLength = 2 ∧
      noDoubleZeroSequenceSchema.recurrenceOrder = 2 := by
  native_decide

theorem words_avoiding_double_zero_counts_upto_eleven :
    List.ofFn (fun n : Fin 12 => wordsAvoidingDoubleZeroCount n.val) =
      [1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233] := by
  native_decide

theorem words_avoiding_double_zero_are_fibonacci_upto_eleven :
    List.ofFn (fun n : Fin 12 => wordsAvoidingDoubleZeroCount n.val) =
      List.ofFn (fun n : Fin 12 => fibonacci (n.val + 2)) := by
  native_decide

end AsymptoticExpansionSchemes
