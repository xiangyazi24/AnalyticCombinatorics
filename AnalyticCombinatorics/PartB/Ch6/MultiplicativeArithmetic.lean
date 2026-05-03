import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace MultiplicativeArithmetic

/-!
Multiplicative arithmetic functions and their finite Dirichlet-coefficient
checks, following the elementary arithmetic-function examples of Chapter VI.
-/

def phiTable : Fin 12 → ℕ := ![1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4]

def mobiusTable : Fin 12 → ℤ := ![1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0]

def sigma0Table : Fin 12 → ℕ := ![1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 6]

def sigma1Table : Fin 12 → ℕ := ![1, 3, 4, 7, 6, 12, 8, 15, 13, 18, 12, 28]

def liouvilleTable : Fin 12 → ℤ := ![1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1]

def omegaTable : Fin 12 → ℕ := ![0, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3]

def phi : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 4
  | 6 => 2
  | 7 => 6
  | 8 => 4
  | 9 => 6
  | 10 => 4
  | 11 => 10
  | 12 => 4
  | _ => 0

def mobius : ℕ → ℤ
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => 0
  | 5 => -1
  | 6 => 1
  | 7 => -1
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => -1
  | 12 => 0
  | _ => 0

def sigma0 : ℕ → ℕ
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 2
  | 6 => 4
  | 7 => 2
  | 8 => 4
  | 9 => 3
  | 10 => 4
  | 11 => 2
  | 12 => 6
  | _ => 0

def sigma1 : ℕ → ℕ
  | 1 => 1
  | 2 => 3
  | 3 => 4
  | 4 => 7
  | 5 => 6
  | 6 => 12
  | 7 => 8
  | 8 => 15
  | 9 => 13
  | 10 => 18
  | 11 => 12
  | 12 => 28
  | _ => 0

def liouville : ℕ → ℤ
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => 1
  | 5 => -1
  | 6 => 1
  | 7 => -1
  | 8 => -1
  | 9 => 1
  | 10 => 1
  | 11 => -1
  | 12 => -1
  | _ => 0

def omega : ℕ → ℕ
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 1
  | 6 => 2
  | 7 => 1
  | 8 => 3
  | 9 => 2
  | 10 => 2
  | 11 => 1
  | 12 => 3
  | _ => 0

def divisorSumNat (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun acc d => if d ≠ 0 ∧ n % d = 0 then acc + f d else acc) 0

def divisorSumInt (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  (List.range (n + 1)).foldl (fun acc d => if d ≠ 0 ∧ n % d = 0 then acc + f d else acc) 0

def singletonOne : ℕ → ℤ
  | 1 => 1
  | _ => 0

def squareIndicator : ℕ → ℤ
  | 1 => 1
  | 4 => 1
  | 9 => 1
  | _ => 0

theorem phi_table_values :
    phiTable 0 = 1 ∧ phiTable 1 = 1 ∧ phiTable 2 = 2 ∧ phiTable 3 = 2 ∧
      phiTable 4 = 4 ∧ phiTable 5 = 2 ∧ phiTable 6 = 6 ∧ phiTable 7 = 4 ∧
      phiTable 8 = 6 ∧ phiTable 9 = 4 ∧ phiTable 10 = 10 ∧ phiTable 11 = 4 := by
  native_decide

theorem phi_values :
    phi 1 = 1 ∧ phi 2 = 1 ∧ phi 3 = 2 ∧ phi 4 = 2 ∧ phi 5 = 4 ∧ phi 6 = 2 ∧
      phi 7 = 6 ∧ phi 8 = 4 ∧ phi 9 = 6 ∧ phi 10 = 4 ∧ phi 11 = 10 ∧ phi 12 = 4 := by
  native_decide

theorem phi_divisor_sums :
    divisorSumNat phi 1 = 1 ∧ divisorSumNat phi 2 = 2 ∧ divisorSumNat phi 3 = 3 ∧
      divisorSumNat phi 4 = 4 ∧ divisorSumNat phi 5 = 5 ∧ divisorSumNat phi 6 = 6 ∧
      divisorSumNat phi 7 = 7 ∧ divisorSumNat phi 8 = 8 ∧ divisorSumNat phi 9 = 9 ∧
      divisorSumNat phi 10 = 10 ∧ divisorSumNat phi 11 = 11 ∧ divisorSumNat phi 12 = 12 := by
  native_decide

theorem mobius_table_values :
    mobiusTable 0 = 1 ∧ mobiusTable 1 = -1 ∧ mobiusTable 2 = -1 ∧ mobiusTable 3 = 0 ∧
      mobiusTable 4 = -1 ∧ mobiusTable 5 = 1 ∧ mobiusTable 6 = -1 ∧
      mobiusTable 7 = 0 ∧ mobiusTable 8 = 0 ∧ mobiusTable 9 = 1 ∧
      mobiusTable 10 = -1 ∧ mobiusTable 11 = 0 := by
  native_decide

theorem mobius_values :
    mobius 1 = 1 ∧ mobius 2 = -1 ∧ mobius 3 = -1 ∧ mobius 4 = 0 ∧
      mobius 5 = -1 ∧ mobius 6 = 1 := by
  native_decide

theorem mobius_divisor_sums :
    divisorSumInt mobius 1 = singletonOne 1 ∧ divisorSumInt mobius 2 = singletonOne 2 ∧
      divisorSumInt mobius 3 = singletonOne 3 ∧ divisorSumInt mobius 4 = singletonOne 4 ∧
      divisorSumInt mobius 5 = singletonOne 5 ∧ divisorSumInt mobius 6 = singletonOne 6 ∧
      divisorSumInt mobius 7 = singletonOne 7 ∧ divisorSumInt mobius 8 = singletonOne 8 ∧
      divisorSumInt mobius 9 = singletonOne 9 ∧ divisorSumInt mobius 10 = singletonOne 10 ∧
      divisorSumInt mobius 11 = singletonOne 11 ∧ divisorSumInt mobius 12 = singletonOne 12 := by
  native_decide

theorem sigma0_values :
    sigma0 1 = 1 ∧ sigma0 2 = 2 ∧ sigma0 3 = 2 ∧ sigma0 4 = 3 ∧
      sigma0 5 = 2 ∧ sigma0 6 = 4 ∧ sigma0 7 = 2 ∧ sigma0 8 = 4 ∧
      sigma0 9 = 3 ∧ sigma0 10 = 4 ∧ sigma0 11 = 2 ∧ sigma0 12 = 6 := by
  native_decide

theorem sigma0_table_values :
    sigma0Table 0 = 1 ∧ sigma0Table 1 = 2 ∧ sigma0Table 2 = 2 ∧ sigma0Table 3 = 3 ∧
      sigma0Table 4 = 2 ∧ sigma0Table 5 = 4 ∧ sigma0Table 6 = 2 ∧
      sigma0Table 7 = 4 ∧ sigma0Table 8 = 3 ∧ sigma0Table 9 = 4 ∧
      sigma0Table 10 = 2 ∧ sigma0Table 11 = 6 := by
  native_decide

theorem sigma1_values :
    sigma1 1 = 1 ∧ sigma1 2 = 3 ∧ sigma1 3 = 4 ∧ sigma1 4 = 7 ∧
      sigma1 5 = 6 ∧ sigma1 6 = 12 ∧ sigma1 7 = 8 ∧ sigma1 8 = 15 ∧
      sigma1 9 = 13 ∧ sigma1 10 = 18 ∧ sigma1 11 = 12 ∧ sigma1 12 = 28 := by
  native_decide

theorem sigma1_table_values :
    sigma1Table 0 = 1 ∧ sigma1Table 1 = 3 ∧ sigma1Table 2 = 4 ∧ sigma1Table 3 = 7 ∧
      sigma1Table 4 = 6 ∧ sigma1Table 5 = 12 ∧ sigma1Table 6 = 8 ∧
      sigma1Table 7 = 15 ∧ sigma1Table 8 = 13 ∧ sigma1Table 9 = 18 ∧
      sigma1Table 10 = 12 ∧ sigma1Table 11 = 28 := by
  native_decide

theorem liouville_values :
    liouville 1 = 1 ∧ liouville 2 = -1 ∧ liouville 3 = -1 ∧ liouville 4 = 1 ∧
      liouville 5 = -1 ∧ liouville 6 = 1 ∧ liouville 7 = -1 ∧ liouville 8 = -1 ∧
      liouville 9 = 1 ∧ liouville 10 = 1 ∧ liouville 11 = -1 ∧ liouville 12 = -1 := by
  native_decide

theorem liouville_table_values :
    liouvilleTable 0 = 1 ∧ liouvilleTable 1 = -1 ∧ liouvilleTable 2 = -1 ∧
      liouvilleTable 3 = 1 ∧ liouvilleTable 4 = -1 ∧ liouvilleTable 5 = 1 ∧
      liouvilleTable 6 = -1 ∧ liouvilleTable 7 = -1 ∧ liouvilleTable 8 = 1 ∧
      liouvilleTable 9 = 1 ∧ liouvilleTable 10 = -1 ∧ liouvilleTable 11 = -1 := by
  native_decide

theorem liouville_divisor_sums :
    divisorSumInt liouville 1 = squareIndicator 1 ∧
      divisorSumInt liouville 2 = squareIndicator 2 ∧
      divisorSumInt liouville 3 = squareIndicator 3 ∧
      divisorSumInt liouville 4 = squareIndicator 4 ∧
      divisorSumInt liouville 5 = squareIndicator 5 ∧
      divisorSumInt liouville 6 = squareIndicator 6 ∧
      divisorSumInt liouville 7 = squareIndicator 7 ∧
      divisorSumInt liouville 8 = squareIndicator 8 ∧
      divisorSumInt liouville 9 = squareIndicator 9 ∧
      divisorSumInt liouville 10 = squareIndicator 10 ∧
      divisorSumInt liouville 11 = squareIndicator 11 ∧
      divisorSumInt liouville 12 = squareIndicator 12 := by
  native_decide

theorem omega_values :
    omega 1 = 0 ∧ omega 2 = 1 ∧ omega 3 = 1 ∧ omega 4 = 2 ∧ omega 5 = 1 ∧
      omega 6 = 2 ∧ omega 7 = 1 ∧ omega 8 = 3 ∧ omega 9 = 2 ∧
      omega 10 = 2 ∧ omega 11 = 1 ∧ omega 12 = 3 := by
  native_decide

theorem omega_table_values :
    omegaTable 0 = 0 ∧ omegaTable 1 = 1 ∧ omegaTable 2 = 1 ∧ omegaTable 3 = 2 ∧
      omegaTable 4 = 1 ∧ omegaTable 5 = 2 ∧ omegaTable 6 = 1 ∧
      omegaTable 7 = 3 ∧ omegaTable 8 = 2 ∧ omegaTable 9 = 2 ∧
      omegaTable 10 = 1 ∧ omegaTable 11 = 3 := by
  native_decide

end MultiplicativeArithmetic
