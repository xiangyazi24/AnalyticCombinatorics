import Mathlib.Tactic
set_option linter.style.nativeDecide false

/-!
# Ch IX -- Queueing networks and service systems

Finite numerical checks for elementary queueing models: M/M/1 steady-state
probabilities, Erlang loss probabilities, tandem queues, two-node Jackson
traffic equations, and Little-law instances.
-/

namespace QueueingNetworks

open Finset

/-! ## 1. M/M/1 steady-state probabilities -/

/-- M/M/1 stationary mass `π_k = (1 - ρ) ρ^k`. -/
def mm1Mass (rho : ℚ) (k : ℕ) : ℚ :=
  (1 - rho) * rho ^ k

/-- The first ten M/M/1 stationary probabilities for `ρ = 1/2`. -/
def mm1HalfSteadyState : Fin 10 → ℚ :=
  ![1 / 2, 1 / 4, 1 / 8, 1 / 16, 1 / 32,
    1 / 64, 1 / 128, 1 / 256, 1 / 512, 1 / 1024]

/-- The table is the geometric stationary law for an M/M/1 queue with `ρ = 1/2`. -/
theorem mm1HalfSteadyState_eq_mass :
    ∀ k : Fin 10, mm1HalfSteadyState k = mm1Mass (1 / 2) k.val := by
  native_decide

/-- Finite partial sum of M/M/1 stationary masses from state `0` through state `n`. -/
def mm1PartialSum (rho : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), mm1Mass rho k

/-- For `ρ = 1/2`, the partial mass through state `n` is `1 - 2^-(n+1)`. -/
theorem mm1HalfPartialSum_eq :
    ∀ n : Fin 10,
      mm1PartialSum (1 / 2) n.val = 1 - (1 / 2 : ℚ) ^ (n.val + 1) := by
  native_decide

/-- Scaled M/M/1 masses: `2^(k+1) π_k = 1` for `ρ = 1/2`. -/
def mm1HalfScaledMass : Fin 10 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- The scaled table records the constant numerator of the geometric law. -/
theorem mm1HalfScaledMass_eq :
    ∀ k : Fin 10,
      (mm1HalfScaledMass k : ℚ) =
        (2 : ℚ) ^ (k.val + 1) * mm1HalfSteadyState k := by
  native_decide

/-! ## 2. Erlang loss probabilities -/

/-- The unnormalized Erlang term `a^n / n!`. -/
def erlangOfferedTerm (a n : ℕ) : ℚ :=
  (a : ℚ) ^ n / (Nat.factorial n : ℚ)

/-- Erlang's loss formula `B(n,a)` for `n` servers and offered load `a`. -/
def erlangLoss (servers a : ℕ) : ℚ :=
  erlangOfferedTerm a servers /
    (∑ k ∈ range (servers + 1), erlangOfferedTerm a k)

/-- `B(n,2)` for `n = 0..6`. -/
def erlangLossTwoErlangs : Fin 7 → ℚ :=
  ![1, 2 / 3, 2 / 5, 4 / 19, 2 / 21, 4 / 109, 4 / 331]

/-- The table computes Erlang's loss formula for offered load `a = 2`. -/
theorem erlangLossTwoErlangs_eq :
    ∀ n : Fin 7, erlangLossTwoErlangs n = erlangLoss n.val 2 := by
  native_decide

/-- `B(n,3)` for `n = 0..6`. -/
def erlangLossThreeErlangs : Fin 7 → ℚ :=
  ![1, 3 / 4, 9 / 17, 9 / 26, 27 / 131, 81 / 736, 81 / 1553]

/-- The table computes Erlang's loss formula for offered load `a = 3`. -/
theorem erlangLossThreeErlangs_eq :
    ∀ n : Fin 7, erlangLossThreeErlangs n = erlangLoss n.val 3 := by
  native_decide

/-- Adding servers lowers the loss probability in these small `a = 2` instances. -/
theorem erlangLossTwoErlangs_decreases :
    erlangLossTwoErlangs 1 < erlangLossTwoErlangs 0 ∧
    erlangLossTwoErlangs 2 < erlangLossTwoErlangs 1 ∧
    erlangLossTwoErlangs 3 < erlangLossTwoErlangs 2 ∧
    erlangLossTwoErlangs 4 < erlangLossTwoErlangs 3 ∧
    erlangLossTwoErlangs 5 < erlangLossTwoErlangs 4 ∧
    erlangLossTwoErlangs 6 < erlangLossTwoErlangs 5 := by
  native_decide

/-! ## 3. Tandem queue state tables -/

/-- Sample number of jobs at station 1 in a tandem two-service system. -/
def tandemStationOneJobs : Fin 10 → ℕ :=
  ![0, 1, 2, 1, 0, 3, 2, 1, 4, 2]

/-- Sample number of jobs at station 2 in the same tandem system. -/
def tandemStationTwoJobs : Fin 10 → ℕ :=
  ![0, 0, 1, 2, 3, 1, 2, 3, 0, 4]

/-- Total number of jobs in the tandem system at the sampled epochs. -/
def tandemTotalJobs : Fin 10 → ℕ :=
  ![0, 1, 3, 3, 3, 4, 4, 4, 4, 6]

/-- The total population is the sum of the two station populations. -/
theorem tandemTotalJobs_eq :
    ∀ t : Fin 10, tandemTotalJobs t = tandemStationOneJobs t + tandemStationTwoJobs t := by
  native_decide

/-- Workload units with station 1 weighted by `2` and station 2 weighted by `1`. -/
def tandemWorkloadUnits : Fin 10 → ℕ :=
  ![0, 2, 5, 4, 3, 7, 6, 5, 8, 8]

/-- The workload table is `2 q_1 + q_2`. -/
theorem tandemWorkloadUnits_eq :
    ∀ t : Fin 10,
      tandemWorkloadUnits t = 2 * tandemStationOneJobs t + tandemStationTwoJobs t := by
  native_decide

/-! ## 4. Two-node Jackson network checks -/

/-- Effective arrival rate at node 1 in a two-node Jackson example. -/
def jacksonLambdaOne : ℚ := 6

/-- Effective arrival rate at node 2 in a two-node Jackson example. -/
def jacksonLambdaTwo : ℚ := 5

/-- Service rate at node 1. -/
def jacksonMuOne : ℚ := 12

/-- Service rate at node 2. -/
def jacksonMuTwo : ℚ := 15

/-- Node 1 traffic equation: `λ₁ = e₁ + p₂₁ λ₂`. -/
theorem jacksonTrafficEquation_one :
    jacksonLambdaOne = 4 + (2 / 5 : ℚ) * jacksonLambdaTwo := by
  native_decide

/-- Node 2 traffic equation: `λ₂ = e₂ + p₁₂ λ₁`. -/
theorem jacksonTrafficEquation_two :
    jacksonLambdaTwo = 2 + (1 / 2 : ℚ) * jacksonLambdaOne := by
  native_decide

/-- Traffic intensities for the two nodes. -/
def jacksonRho : Fin 2 → ℚ :=
  ![1 / 2, 1 / 3]

/-- The stored traffic intensities are `λ_i / μ_i`. -/
theorem jacksonRho_eq_lambda_div_mu :
    jacksonRho 0 = jacksonLambdaOne / jacksonMuOne ∧
    jacksonRho 1 = jacksonLambdaTwo / jacksonMuTwo := by
  native_decide

/-- First coordinate of six small two-node Jackson states. -/
def jacksonStateNodeOne : Fin 6 → ℕ :=
  ![0, 1, 0, 2, 1, 0]

/-- Second coordinate of six small two-node Jackson states. -/
def jacksonStateNodeTwo : Fin 6 → ℕ :=
  ![0, 0, 1, 0, 1, 2]

/-- Product-form stationary mass for the `ρ₁ = 1/2`, `ρ₂ = 1/3` example. -/
def jacksonProductMass (i j : ℕ) : ℚ :=
  (1 - (1 / 2 : ℚ)) * (1 - (1 / 3 : ℚ)) *
    (1 / 2 : ℚ) ^ i * (1 / 3 : ℚ) ^ j

/-- Product-form masses for the six stored states. -/
def jacksonProductMassTable : Fin 6 → ℚ :=
  ![1 / 3, 1 / 6, 1 / 9, 1 / 12, 1 / 18, 1 / 27]

/-- The table matches the product-form probabilities for the stored states. -/
theorem jacksonProductMassTable_eq :
    ∀ s : Fin 6,
      jacksonProductMassTable s =
        jacksonProductMass (jacksonStateNodeOne s) (jacksonStateNodeTwo s) := by
  native_decide

/-! ## 5. Little-law verification instances -/

/-- Arrival rates in six small service-system examples. -/
def littleArrivalRate : Fin 6 → ℚ :=
  ![1 / 2, 2 / 3, 3 / 4, 4 / 5, 5 / 6, 3 / 2]

/-- Mean sojourn times in the same six examples. -/
def littleMeanSojournTime : Fin 6 → ℚ :=
  ![4, 3, 8 / 3, 5 / 2, 12 / 5, 2]

/-- Mean number in system for the six Little-law examples. -/
def littleMeanNumber : Fin 6 → ℚ :=
  ![2, 2, 2, 2, 2, 3]

/-- Little's law `L = λ W` on the stored examples. -/
theorem littleLawTable_eq :
    ∀ s : Fin 6,
      littleMeanNumber s = littleArrivalRate s * littleMeanSojournTime s := by
  native_decide

/-- Arrival rates for four M/M/1 examples. -/
def mm1ArrivalRate : Fin 4 → ℚ :=
  ![1 / 4, 1 / 3, 1 / 2, 2 / 3]

/-- Service rates for four M/M/1 examples. -/
def mm1ServiceRate : Fin 4 → ℚ :=
  ![1 / 2, 1 / 2, 1, 1]

/-- Mean number in system `ρ/(1-ρ)` for the four M/M/1 examples. -/
def mm1MeanNumber : Fin 4 → ℚ :=
  ![1, 2, 1, 2]

/-- M/M/1 mean sojourn time `1/(μ-λ)` for the four examples. -/
def mm1MeanSojournTime : Fin 4 → ℚ :=
  ![4, 6, 2, 3]

/-- Little's law for four M/M/1 parameter choices. -/
theorem littleLawMm1Table_eq :
    ∀ s : Fin 4,
      mm1MeanNumber s = mm1ArrivalRate s * mm1MeanSojournTime s := by
  native_decide

/-- The M/M/1 delay table is `1/(μ-λ)` on the stored examples. -/
theorem mm1MeanSojournTime_eq :
    ∀ s : Fin 4,
      mm1MeanSojournTime s = 1 / (mm1ServiceRate s - mm1ArrivalRate s) := by
  native_decide

end QueueingNetworks
