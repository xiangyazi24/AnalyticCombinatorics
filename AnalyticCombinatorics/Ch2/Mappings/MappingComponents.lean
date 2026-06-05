import Mathlib
import AnalyticCombinatorics.Ch2.Mappings.ConnectedMappings
import AnalyticCombinatorics.Ch2.Mappings.ForestCountComplete
import AnalyticCombinatorics.Ch2.Mappings.RamanujanQ

/-!
# Components of random mappings

The component count is defined as the number of nonempty single-cycle
restrictions of the permutation induced by a mapping on its periodic core.  A
candidate cycle `C` of a map is counted exactly when the ambient map restricts
to a cyclic permutation on `C`; this is equivalent to being one cycle of the
periodic-core permutation.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

/-- A nonempty labelled set together with a cyclic permutation on it. -/
abbrev CandidateCycle (n : ℕ) : Type :=
  Sigma fun C : {C : Finset (Fin n) // C.Nonempty} =>
    {σ : Equiv.Perm C.1 // PermSingleCycle σ}

def candidateSupport {n : ℕ} (A : CandidateCycle n) : Finset (Fin n) :=
  A.1.1

def candidatePerm {n : ℕ} (A : CandidateCycle n) : Equiv.Perm (candidateSupport A) :=
  A.2.1

def candidateCard {n : ℕ} (A : CandidateCycle n) : ℕ :=
  (candidateSupport A).card

abbrev MapsRespectingCandidate {n : ℕ} (A : CandidateCycle n) : Type :=
  {f : Fin n → Fin n // ∀ x : candidateSupport A, f x.1 = (candidatePerm A x : Fin n)}

/--
The same candidate cycles, but stated on the periodic core: all labels of the
support are periodic, and the restriction of `periodicCorePerm f` to that
support is the candidate cyclic permutation.
-/
abbrev CoreCycleOfMap {n : ℕ} (f : Fin n → Fin n) : Type :=
  {A : CandidateCycle n //
    ∃ hper : ∀ x : candidateSupport A, PeriodicPoint f x.1,
      ∀ x : candidateSupport A,
        ((periodicCorePerm f) ⟨x.1, hper x⟩ : Fin n) = (candidatePerm A x : Fin n)}

@[reducible] def coreCycleOfMapFintype {n : ℕ} (f : Fin n → Fin n) :
    Fintype (CoreCycleOfMap f) := by
  classical
  exact Fintype.ofFinite (CoreCycleOfMap f)

/-- The number of connected components of the functional graph of `f`. -/
def componentCount {n : ℕ} (f : Fin n → Fin n) : ℕ :=
  @Fintype.card (CoreCycleOfMap f) (coreCycleOfMapFintype f)

lemma candidate_iterate {n : ℕ} {f : Fin n → Fin n} {A : CandidateCycle n}
    (hA : ∀ x : candidateSupport A, f x.1 = (candidatePerm A x : Fin n))
    (x : candidateSupport A) :
    ∀ m : ℕ, f^[m] x.1 = ((candidatePerm A)^[m] x : Fin n)
  | 0 => rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply']
      rw [candidate_iterate hA x m]
      rw [hA ((candidatePerm A)^[m] x)]
      rw [Function.iterate_succ_apply']

lemma periodicPoint_of_respects_candidate {n : ℕ} {f : Fin n → Fin n}
    {A : CandidateCycle n}
    (hA : ∀ x : candidateSupport A, f x.1 = (candidatePerm A x : Fin n))
    (x : candidateSupport A) :
    PeriodicPoint f x.1 := by
  refine ⟨orderOf (candidatePerm A), orderOf_pos (candidatePerm A), ?_⟩
  calc
    f^[orderOf (candidatePerm A)] x.1 =
        ((candidatePerm A)^[orderOf (candidatePerm A)] x : Fin n) := by
          exact candidate_iterate hA x (orderOf (candidatePerm A))
    _ = x.1 := by
          have hpow : (candidatePerm A) ^ orderOf (candidatePerm A) = 1 :=
            pow_orderOf_eq_one (candidatePerm A)
          have hfun : (candidatePerm A)^[orderOf (candidatePerm A)] x = x := by
            rw [← Equiv.Perm.coe_pow, hpow]
            rfl
          exact congrArg Subtype.val hfun

abbrev MapCycleOfMap {n : ℕ} (f : Fin n → Fin n) : Type :=
  {A : CandidateCycle n //
    ∀ x : candidateSupport A, f x.1 = (candidatePerm A x : Fin n)}

/--
Core-cycle candidates are exactly the ambient cyclic restrictions `f|C = σ_C`.
The reverse direction uses the fact that every point of such a restriction is
periodic, so `periodicCorePerm f` is defined on the support.
-/
def coreCycleMapCycleEquiv {n : ℕ} (f : Fin n → Fin n) :
    CoreCycleOfMap f ≃ MapCycleOfMap f where
  toFun A := by
    rcases A with ⟨A, hcore⟩
    let hper := Classical.choose hcore
    let hcore := Classical.choose_spec hcore
    refine ⟨A, ?_⟩
    intro x
    have hx := hcore x
    simpa using hx
  invFun A := by
    rcases A with ⟨A, hA⟩
    let hper : ∀ x : candidateSupport A, PeriodicPoint f x.1 :=
      fun x => periodicPoint_of_respects_candidate hA x
    refine ⟨A, ⟨hper, ?_⟩⟩
    intro x
    simpa using hA x
  left_inv A := by
    apply Subtype.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    rfl

lemma componentCount_eq_mapCycle_card {n : ℕ} (f : Fin n → Fin n) :
    componentCount f = Fintype.card (MapCycleOfMap f) := by
  exact @Fintype.card_congr (CoreCycleOfMap f) (MapCycleOfMap f)
    (coreCycleOfMapFintype f) inferInstance (coreCycleMapCycleEquiv f)

def mapCycleSwapEquiv (n : ℕ) :
    (Sigma fun f : Fin n → Fin n => MapCycleOfMap f) ≃
      (Sigma fun A : CandidateCycle n => MapsRespectingCandidate A) where
  toFun P := ⟨P.2.1, ⟨P.1, P.2.2⟩⟩
  invFun P := ⟨P.2.1, ⟨P.1, P.2.2⟩⟩
  left_inv P := by
    rcases P with ⟨f, A, hA⟩
    rfl
  right_inv P := by
    rcases P with ⟨A, f, hA⟩
    rfl

def mapsRespectingCandidateEquiv {n : ℕ} (A : CandidateCycle n) :
    MapsRespectingCandidate A ≃ ({x : Fin n // x ∉ candidateSupport A} → Fin n) where
  toFun F := fun x => F.1 x.1
  invFun g := by
    refine ⟨(fun x =>
      if hx : x ∈ candidateSupport A then
        (candidatePerm A ⟨x, hx⟩ : Fin n)
      else
        g ⟨x, hx⟩), ?_⟩
    intro x
    simp
  left_inv F := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ candidateSupport A
    · simp [hx, F.2 ⟨x, hx⟩]
    · simp [hx]
  right_inv g := by
    funext x
    simp [x.2]

lemma card_mapsRespectingCandidate {n : ℕ} (A : CandidateCycle n) :
    Fintype.card (MapsRespectingCandidate A) =
      n ^ (n - candidateCard A) := by
  classical
  calc
    Fintype.card (MapsRespectingCandidate A) =
        Fintype.card ({x : Fin n // x ∉ candidateSupport A} → Fin n) := by
          exact Fintype.card_congr (mapsRespectingCandidateEquiv A)
    _ = n ^ Fintype.card {x : Fin n // x ∉ candidateSupport A} := by
          rw [Fintype.card_fun, Fintype.card_fin]
    _ = n ^ (n - candidateCard A) := by
          congr 1
          change Fintype.card {x : Fin n // x ∉ candidateSupport A} =
            n - (candidateSupport A).card
          rw [Fintype.card_subtype_compl (fun x : Fin n => x ∈ candidateSupport A)]
          simp [Fintype.card_fin]

lemma sum_componentCount_eq_candidate_maps (n : ℕ) :
    (∑ f : Fin n → Fin n, componentCount f) =
      ∑ A : CandidateCycle n, Fintype.card (MapsRespectingCandidate A) := by
  classical
  calc
    (∑ f : Fin n → Fin n, componentCount f) =
        ∑ f : Fin n → Fin n, Fintype.card (MapCycleOfMap f) := by
          refine Finset.sum_congr rfl ?_
          intro f _
          exact componentCount_eq_mapCycle_card f
    _ = Fintype.card (Sigma fun f : Fin n → Fin n => MapCycleOfMap f) := by
          exact Fintype.card_sigma.symm
    _ = Fintype.card (Sigma fun A : CandidateCycle n => MapsRespectingCandidate A) := by
          exact Fintype.card_congr (mapCycleSwapEquiv n)
    _ = ∑ A : CandidateCycle n, Fintype.card (MapsRespectingCandidate A) := by
          exact Fintype.card_sigma

lemma candidate_maps_sum_by_card (n : ℕ) :
    (∑ A : CandidateCycle n, Fintype.card (MapsRespectingCandidate A)) =
      ∑ k ∈ Finset.Icc 1 n,
        Nat.choose n k * (k - 1).factorial * n ^ (n - k) := by
  classical
  calc
    (∑ A : CandidateCycle n, Fintype.card (MapsRespectingCandidate A)) =
        ∑ A : CandidateCycle n, n ^ (n - candidateCard A) := by
          refine Finset.sum_congr rfl ?_
          intro A _
          exact card_mapsRespectingCandidate A
    _ =
        ∑ C : {C : Finset (Fin n) // C.Nonempty},
          ∑ σ : {σ : Equiv.Perm C.1 // PermSingleCycle σ},
            n ^ (n - C.1.card) := by
          rw [Fintype.sum_sigma]
          rfl
    _ =
        ∑ C : {C : Finset (Fin n) // C.Nonempty},
          (C.1.card - 1).factorial * n ^ (n - C.1.card) := by
          refine Finset.sum_congr rfl ?_
          intro C _
          simp [card_permSingleCycle, Fintype.card_coe, mul_comm]
    _ =
        ∑ i ∈ Finset.range n,
          Nat.choose n (i + 1) *
            ((i + 1 - 1).factorial * n ^ (n - (i + 1))) := by
          simpa [Fintype.card_fin] using
            (AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete.sum_nonempty_finsets_by_card
              (β := Fin n)
              (f := fun k : ℕ => (k - 1).factorial * n ^ (n - k)))
    _ =
        ∑ k ∈ Finset.Icc 1 n,
          Nat.choose n k * (k - 1).factorial * n ^ (n - k) := by
          simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc, mul_assoc] using
            (Finset.sum_Ico_eq_sum_range
              (f := fun k : ℕ =>
                Nat.choose n k * (k - 1).factorial * n ^ (n - k))
              1 (n + 1)).symm

theorem sum_componentCount_eq (n : ℕ) :
    (∑ f : Fin n → Fin n, componentCount f) =
      ∑ k ∈ Finset.Icc 1 n,
        Nat.choose n k * (k - 1).factorial * n ^ (n - k) := by
  rw [sum_componentCount_eq_candidate_maps n, candidate_maps_sum_by_card n]

lemma descFactorial_eq_k_mul_choose_mul_pred_factorial {n k : ℕ} (hk : 0 < k) :
    n.descFactorial k = k * (Nat.choose n k * (k - 1).factorial) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  simp [Nat.factorial_succ]
  ring

lemma expectation_term_eq_desc {n k : ℕ} (hn : 0 < n)
    (hk : k ∈ Finset.Icc 1 n) :
    (((Nat.choose n k * (k - 1).factorial * n ^ (n - k) : ℕ) : ℝ) /
        (n : ℝ) ^ n) =
      (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ) ^ k) := by
  have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkle : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hkne : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hkpos
  have htail_ne : (n : ℝ) ^ (n - k) ≠ 0 := pow_ne_zero _ hnne
  have hpowk_ne : (n : ℝ) ^ k ≠ 0 := pow_ne_zero _ hnne
  have hsplit : n = (n - k) + k := by omega
  have hpow_split : (n : ℝ) ^ n = (n : ℝ) ^ (n - k) * (n : ℝ) ^ k := by
    calc
      (n : ℝ) ^ n = (n : ℝ) ^ ((n - k) + k) := by
        exact congrArg (fun e : ℕ => (n : ℝ) ^ e) hsplit
      _ = (n : ℝ) ^ (n - k) * (n : ℝ) ^ k := by
        rw [pow_add]
  have hdesc :
      (n.descFactorial k : ℝ) =
        (k : ℝ) * ((Nat.choose n k * (k - 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast descFactorial_eq_k_mul_choose_mul_pred_factorial (n := n) (k := k) hkpos
  rw [hpow_split, hdesc]
  push_cast
  field_simp [hkne, htail_ne, hpowk_ne]

/-- Exact expected number of components in a uniform random mapping on `n` labels. -/
theorem expected_components_eq {n : ℕ} (hn : 0 < n) :
    (∑ f : Fin n → Fin n, (componentCount f : ℝ)) / (n : ℝ)^n
      = ∑ k ∈ Finset.Icc 1 n,
          (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k) := by
  classical
  have hsum_nat := sum_componentCount_eq n
  have hsum_real :
      (∑ f : Fin n → Fin n, (componentCount f : ℝ)) =
        ∑ k ∈ Finset.Icc 1 n,
          ((Nat.choose n k * (k - 1).factorial * n ^ (n - k) : ℕ) : ℝ) := by
    exact_mod_cast hsum_nat
  calc
    (∑ f : Fin n → Fin n, (componentCount f : ℝ)) / (n : ℝ)^n =
        (∑ k ∈ Finset.Icc 1 n,
          ((Nat.choose n k * (k - 1).factorial * n ^ (n - k) : ℕ) : ℝ)) /
            (n : ℝ)^n := by
          rw [hsum_real]
    _ =
        ∑ k ∈ Finset.Icc 1 n,
          (((Nat.choose n k * (k - 1).factorial * n ^ (n - k) : ℕ) : ℝ) /
            (n : ℝ)^n) := by
          rw [Finset.sum_div]
    _ =
        ∑ k ∈ Finset.Icc 1 n,
          (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact expectation_term_eq_desc hn hk

def componentExpectationFormula (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k)

def weightedRamanujanComponents (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ramanujanQTerm n i / ((i + 1 : ℕ) : ℝ)

lemma descFactorial_succ_eq_mul_pred {n i : ℕ} (hi : i < n) :
    n.descFactorial (i + 1) = n * (n - 1).descFactorial i := by
  have h := Nat.succ_descFactorial_succ (n - 1) i
  have hnpos : 0 < n := by omega
  have hnsucc : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
  simpa [hnsucc, Nat.add_comm] using h

lemma component_formula_term_eq_ramanujan {n i : ℕ} (hn : 0 < n)
    (hi : i ∈ Finset.range n) :
    (n.descFactorial (i + 1) : ℝ) /
        (((i + 1 : ℕ) : ℝ) * (n : ℝ) ^ (i + 1)) =
      ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ)) := by
  have hilt : i < n := Finset.mem_range.mp hi
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hi1ne : (((i + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hpowi_ne : (n : ℝ) ^ i ≠ 0 := pow_ne_zero _ hnne
  rw [ramanujanQTerm_eq_descFactorial_div hn hilt]
  rw [descFactorial_succ_eq_mul_pred (n := n) (i := i) hilt]
  push_cast
  rw [pow_succ]
  field_simp [hnne, hi1ne, hpowi_ne]

theorem componentExpectationFormula_eq_weightedRamanujan {n : ℕ} (hn : 0 < n) :
    componentExpectationFormula n = weightedRamanujanComponents n := by
  classical
  unfold componentExpectationFormula weightedRamanujanComponents
  have hreindex :
      (∑ k ∈ Finset.Icc 1 n,
          (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k)) =
        ∑ i ∈ Finset.range n,
          (n.descFactorial (i + 1) : ℝ) /
            (((i + 1 : ℕ) : ℝ) * (n : ℝ)^(i + 1)) := by
    simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using
      (Finset.sum_Ico_eq_sum_range
        (f := fun k : ℕ =>
          (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k))
        1 (n + 1))
  rw [hreindex]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact component_formula_term_eq_ramanujan hn hi

lemma harmonic_real_eq_sum_inv (n : ℕ) :
    (harmonic n : ℝ) =
      ∑ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ)⁻¹) := by
  simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem weightedRamanujanComponents_le_harmonic (n : ℕ) :
    weightedRamanujanComponents n ≤ (harmonic n : ℝ) := by
  classical
  unfold weightedRamanujanComponents
  calc
    (∑ i ∈ Finset.range n, ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤
        ∑ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ)⁻¹) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hle := ramanujanQTerm_le_one (n := n) (k := i)
            (Nat.le_of_lt (Finset.mem_range.mp hi))
          have hden : 0 ≤ (((i + 1 : ℕ) : ℝ)) := by positivity
          have h := div_le_div_of_nonneg_right hle hden
          simpa [one_div] using h
    _ = (harmonic n : ℝ) := by
          exact (harmonic_real_eq_sum_inv n).symm

lemma half_harmonic_eq_sum_half_inv (m : ℕ) :
    ((harmonic m : ℝ) / 2) =
      ∑ i ∈ Finset.range m, (1 / 2 : ℝ) / (((i + 1 : ℕ) : ℝ)) := by
  rw [harmonic_real_eq_sum_inv, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hden : (((i + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hden]

theorem half_harmonic_sqrt_le_weightedRamanujan (n : ℕ) :
    ((harmonic (Nat.sqrt n) : ℝ) / 2) ≤ weightedRamanujanComponents n := by
  classical
  unfold weightedRamanujanComponents
  have hsubset : Finset.range (Nat.sqrt n) ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.sqrt_le_self n))
  calc
    ((harmonic (Nat.sqrt n) : ℝ) / 2) =
        ∑ i ∈ Finset.range (Nat.sqrt n), (1 / 2 : ℝ) / (((i + 1 : ℕ) : ℝ)) := by
          exact half_harmonic_eq_sum_half_inv (Nat.sqrt n)
    _ ≤ ∑ i ∈ Finset.range (Nat.sqrt n),
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hterm := ramanujanQTerm_ge_half_of_lt_sqrt (n := n) (k := i)
            (Finset.mem_range.mp hi)
          have hden : 0 ≤ (((i + 1 : ℕ) : ℝ)) := by positivity
          exact div_le_div_of_nonneg_right hterm hden
    _ ≤ ∑ i ∈ Finset.range n, ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
          intro i hiBig _hiSmall
          have hi : i < n := Finset.mem_range.mp hiBig
          have hnonneg := ramanujanQTerm_nonneg (n := n) (k := i) (Nat.le_of_lt hi)
          have hden : 0 ≤ (((i + 1 : ℕ) : ℝ)) := by positivity
          exact div_nonneg hnonneg hden

theorem componentExpectationFormula_le_harmonic {n : ℕ} (hn : 0 < n) :
    componentExpectationFormula n ≤ (harmonic n : ℝ) := by
  rw [componentExpectationFormula_eq_weightedRamanujan hn]
  exact weightedRamanujanComponents_le_harmonic n

theorem half_harmonic_sqrt_le_componentExpectationFormula {n : ℕ} (hn : 0 < n) :
    ((harmonic (Nat.sqrt n) : ℝ) / 2) ≤ componentExpectationFormula n := by
  rw [componentExpectationFormula_eq_weightedRamanujan hn]
  exact half_harmonic_sqrt_le_weightedRamanujan n

theorem expected_components_one :
    (∑ f : Fin 1 → Fin 1, (componentCount f : ℝ)) / (1 : ℝ)^1 = 1 := by
  calc
    (∑ f : Fin 1 → Fin 1, (componentCount f : ℝ)) / (1 : ℝ)^1 =
        ∑ k ∈ Finset.Icc 1 1,
          (Nat.descFactorial 1 k : ℝ) / ((k : ℝ) * (1 : ℝ)^k) := by
          simpa using expected_components_eq (n := 1) (by norm_num)
    _ = 1 := by
          norm_num [Nat.descFactorial_eq_factorial_mul_choose]

theorem expected_components_two :
    (∑ f : Fin 2 → Fin 2, (componentCount f : ℝ)) / (2 : ℝ)^2 = 5 / 4 := by
  calc
    (∑ f : Fin 2 → Fin 2, (componentCount f : ℝ)) / (2 : ℝ)^2 =
        ∑ k ∈ Finset.Icc 1 2,
          (Nat.descFactorial 2 k : ℝ) / ((k : ℝ) * (2 : ℝ)^k) := by
          simpa using expected_components_eq (n := 2) (by norm_num)
    _ = 5 / 4 := by
          have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by
            ext x
            simp
            omega
          rw [hIcc]
          norm_num [Nat.descFactorial_eq_factorial_mul_choose]

end

end AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS
