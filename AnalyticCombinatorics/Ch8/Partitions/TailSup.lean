import AnalyticCombinatorics.Ch8.Partitions.StepSummable

/-!
# R7 Fact B via Doeblin: the tail-sup of block oscillation is summable

The §9 connection's key device: if block oscillation `W ≥ 0` is bounded and satisfies the slab
contraction `W R ≤ q · sSup(W '' {s ≥ R−B})` (`0 ≤ q < 1`), then its tail-sup
`V R := sSup(W '' {s ≥ R})` is monotone-dominated, so `V R ≤ q · V(R−B)`, hence `Summable V`.  This
turns the local (comparable-rank) contraction into a global summable bound, resolving the far-pair
obstruction.  `csSup`-based.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

lemma tailsup_summable {W : ℕ → ℝ} {q M : ℝ} {B : ℕ}
    (hWnn : ∀ R, 0 ≤ W R) (hWbd : ∀ R, W R ≤ M)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ R, W R ≤ q * sSup (W '' {s | R - B ≤ s})) :
    Summable (fun R => sSup (W '' {s | R ≤ s})) := by
  set V := fun R => sSup (W '' {s | R ≤ s}) with hV
  have hbdd : ∀ R, BddAbove (W '' {s | R ≤ s}) := by
    intro R; exact ⟨M, by rintro _ ⟨s, _, rfl⟩; exact hWbd s⟩
  have hbdd' : ∀ R, BddAbove (W '' {s | R - B ≤ s}) := by
    intro R; exact ⟨M, by rintro _ ⟨s, _, rfl⟩; exact hWbd s⟩
  have hmem : ∀ R, W R ∈ W '' {s | R ≤ s} := fun R => ⟨R, le_refl R, rfl⟩
  have hWleV : ∀ R, W R ≤ V R := fun R => le_csSup (hbdd R) (hmem R)
  have hVnn : ∀ R, 0 ≤ V R := fun R => (hWnn R).trans (hWleV R)
  -- antitone: smaller index ⟹ larger sup
  have hVanti : ∀ {a b : ℕ}, a ≤ b → V b ≤ V a := by
    intro a b hab
    refine csSup_le_csSup (hbdd a) ⟨W b, hmem b⟩ ?_
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, le_trans hab hs, rfl⟩
  -- the contraction on V
  have hVcontract : ∀ R, V R ≤ q * V (R - B) := by
    intro R
    refine csSup_le ⟨W R, hmem R⟩ ?_
    rintro _ ⟨s, (hs : R ≤ s), rfl⟩
    calc W s ≤ q * sSup (W '' {s' | s - B ≤ s'}) := hcontract s
      _ ≤ q * V (R - B) := by
          apply mul_le_mul_of_nonneg_left _ hq0
          exact hVanti (by omega)
  -- summability via the B-step contraction V(n+B) ≤ q V(n)
  apply summable_of_step_le hVnn hq1 hq0
  intro n
  have := hVcontract (n + B)
  simpa using this

end AnalyticCombinatorics.Ch8.Partitions.Erdos
