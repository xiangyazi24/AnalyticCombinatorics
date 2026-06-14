import AnalyticCombinatorics.Ch5.ContinuedFractions.FlajoletPathSum

/-!
# Ch5 §V — Flajolet's continued fraction theorem: removing the height bound

`Flajolet.lean` / `FlajoletPathSum.lean` prove the **bounded-height** form
`flajolet_cf` / `coeff_JFraction_eq_pathSum`: for every height bound `h`, the
height-`h` J-fraction's coefficients are the height-`h` Motzkin path sums.

The bound is immaterial for the coefficient of `z^n`: a Motzkin path of length
`n` (which returns to level 0) can never reach relative height above `n`, so the
length-`n` coefficient stabilizes once `h ≥ n`. This file proves that
stabilization, lifting the theorem off the height restriction:

* `Wcoeff_height_indep` — `Wcoeff h a b c n = Wcoeff k a b c n` whenever
  `n ≤ h` and `n ≤ k` (the coefficient is independent of the height bound
  above the length).
* `coeff_JFraction_height_indep` — the height-`h` J-fraction's `z^n` coefficient
  equals the height-`n` one for any `h ≥ n`; i.e. the bounded J-fraction agrees
  with the full (unbounded) continued fraction in every coefficient.
-/

open scoped BigOperators PowerSeries

namespace AnalyticCombinatorics.Ch5.ContinuedFractions

/-- The height-`h` coefficient of length `n` does not depend on the height bound,
provided the bound is at least the length (a length-`n` path never exceeds
relative height `n`). Strong induction on the length. -/
theorem Wcoeff_height_indep {R : Type*} [CommRing R] :
    ∀ (n h k : ℕ) (a b c : ℕ → R), n ≤ h → n ≤ k →
      Wcoeff h a b c n = Wcoeff k a b c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h k a b c hh hk
    rcases n with _ | _ | m
    · -- n = 0
      simp
    · -- n = 1
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Wcoeff_succ_one, Wcoeff_succ_one]
    · -- n = m + 2
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have e1 : Wcoeff (h' + 1) a b c (m + 1) = Wcoeff (k' + 1) a b c (m + 1) :=
        ih (m + 1) (by omega) (h' + 1) (k' + 1) a b c (by omega) (by omega)
      have e2 : ∀ i : Fin (m + 1),
          Wcoeff h' (shift a) (shift b) (shift c) i.1
            = Wcoeff k' (shift a) (shift b) (shift c) i.1 := fun i =>
        ih i.1 (by have := i.2; omega) h' k' (shift a) (shift b) (shift c)
          (by have := i.2; omega) (by have := i.2; omega)
      have e3 : ∀ i : Fin (m + 1),
          Wcoeff (h' + 1) a b c (m - i.1) = Wcoeff (k' + 1) a b c (m - i.1) := fun i =>
        ih (m - i.1) (by have := i.2; omega) (h' + 1) (k' + 1) a b c
          (by omega) (by omega)
      have hsum :
          (∑ i : Fin (m + 1),
              Wcoeff h' (shift a) (shift b) (shift c) i.1
                * Wcoeff (h' + 1) a b c (m - i.1))
            = (∑ i : Fin (m + 1),
              Wcoeff k' (shift a) (shift b) (shift c) i.1
                * Wcoeff (k' + 1) a b c (m - i.1)) :=
        Finset.sum_congr rfl (fun i _ => by rw [e2 i, e3 i])
      rw [Wcoeff_succ_succ, Wcoeff_succ_succ, e1, hsum]

/-- The height-`h` coefficient of length `n` equals the height-`n` value
(for `h ≥ n`): the canonical height-bounded representative of the unbounded
coefficient. -/
theorem Wcoeff_eq_at_length {R : Type*} [CommRing R]
    (h n : ℕ) (a b c : ℕ → R) (hn : n ≤ h) :
    Wcoeff h a b c n = Wcoeff n a b c n :=
  Wcoeff_height_indep n h n a b c hn le_rfl

open AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum in
/-- **Unbounded continued fraction theorem (coefficient form).** For `h ≥ n`,
the height-`h` J-fraction's `z^n` coefficient is independent of the height
bound `h` — it equals the height-`n` value. Hence the bounded J-fractions form
a coherent system whose coefficients are the full (height-unrestricted) Motzkin
path sums. -/
theorem coeff_JFraction_height_indep {R : Type*} [CommRing R]
    (h n : ℕ) (a b c : ℕ → R) (hn : n ≤ h) :
    PowerSeries.coeff (R := R) n (JFraction h a b c)
      = PowerSeries.coeff (R := R) n (JFraction n a b c) := by
  rw [coeff_JFraction_eq_pathSum, coeff_JFraction_eq_pathSum,
    WpathSum_eq_Wcoeff, WpathSum_eq_Wcoeff, Wcoeff_eq_at_length h n a b c hn]

end AnalyticCombinatorics.Ch5.ContinuedFractions

-- Axiom audit (must be exactly {propext, Classical.choice, Quot.sound}):
#print axioms AnalyticCombinatorics.Ch5.ContinuedFractions.Wcoeff_height_indep
#print axioms AnalyticCombinatorics.Ch5.ContinuedFractions.coeff_JFraction_height_indep
