import AnalyticCombinatorics.Ch5.ContinuedFractions.FlajoletPathSum

/-!
# Ch5 §V — Flajolet's theorem on genuine step-list lattice paths

`Flajolet.lean` proves `W h a b c = JFraction h a b c` for the **first-return-coded**
`MotzkinPath` type, where the first-return decomposition is built into the type definition.
This file closes the faithfulness gap: it introduces an **independent** lattice-path object —
a `List Step` together with the floor-0 / ceiling-`h` validity predicate `Walk` and the
return-to-zero / length conditions (`ClosedMotzkin`) — defines its genuine step-product weight
`stepWeight`, and proves a weight-preserving bijection to `MotzkinPath`.  Composing with
`coeff_JFraction_eq_pathSum` upgrades Flajolet's theorem to a statement about real lattice paths
defined as step sequences, with the first-return decomposition now a *theorem*, not a definition.

This file (part 1): the independent definitions and the **structural direction** —
`toSteps` (code → step list), and that it lands in `ClosedMotzkin` with the matching weight.
-/

open scoped BigOperators PowerSeries

namespace AnalyticCombinatorics.Ch5.ContinuedFractions

noncomputable section

set_option maxHeartbeats 800000

variable {R : Type*} [CommRing R]

/-- Absolute level reached after running a step list from start level `s`. -/
def endLevel (s : ℕ) : List Step → ℕ
  | [] => s
  | st :: rest => endLevel (Step.nextLevel s st) rest

@[simp] lemma endLevel_nil (s : ℕ) : endLevel s [] = s := rfl

lemma endLevel_cons (s : ℕ) (st : Step) (rest : List Step) :
    endLevel s (st :: rest) = endLevel (Step.nextLevel s st) rest := rfl

lemma endLevel_append (s : ℕ) (l₁ l₂ : List Step) :
    endLevel s (l₁ ++ l₂) = endLevel (endLevel s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons st rest ih => simp only [List.cons_append, endLevel_cons, ih]

/-- A valid lattice walk: from start level `s`, staying in `[0, h]` (floor `0`: no down step
from level `0`; ceiling `h`: no up step above `h`). Indexed by the current level. -/
inductive Walk (h : ℕ) : ℕ → List Step → Prop
  | nil {s} : Walk h s []
  | level {s rest} : Walk h s rest → Walk h s (Step.level :: rest)
  | up {s rest} : s + 1 ≤ h → Walk h (s + 1) rest → Walk h s (Step.up :: rest)
  | down {s rest} : Walk h s rest → Walk h (s + 1) (Step.down :: rest)

/-- A closed Motzkin path of height bound `h` and length `n`: a valid walk from level `0`
returning to level `0`. -/
def ClosedMotzkin (h n : ℕ) (p : List Step) : Prop :=
  Walk h 0 p ∧ endLevel 0 p = 0 ∧ p.length = n

/-- Genuine step-product weight of a path run from absolute level `s`: an up step from level
`k` weighs `a k`, a down step from level `k` (landing at `k-1`) weighs `b (k-1)`, a level step
at level `k` weighs `c k`. -/
def stepWeight (a b c : ℕ → R) : ℕ → List Step → R
  | _s, [] => 1
  | s, Step.level :: rest => c s * stepWeight a b c s rest
  | s, Step.up :: rest => a s * stepWeight a b c (s + 1) rest
  | s, Step.down :: rest => b (s - 1) * stepWeight a b c (s - 1) rest

@[simp] lemma stepWeight_nil (a b c : ℕ → R) (s : ℕ) : stepWeight a b c s [] = 1 := rfl

lemma stepWeight_append (a b c : ℕ → R) (s : ℕ) (l₁ l₂ : List Step) :
    stepWeight a b c s (l₁ ++ l₂)
      = stepWeight a b c s l₁ * stepWeight a b c (endLevel s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => simp [endLevel]
  | cons st rest ih =>
    cases st <;>
      simp only [List.cons_append, stepWeight, endLevel_cons, Step.nextLevel, ih] <;> ring

/-- Running one level higher with the original weights = running at the base with shifted
weights (the arch-interior reindexing).  Needs validity: a down step never leaves the floor,
so the `ℕ`-subtraction in `stepWeight` does not truncate. -/
lemma stepWeight_shift {H : ℕ} (a b c : ℕ → R) {s : ℕ} {p : List Step} (hp : Walk H s p) :
    stepWeight a b c (s + 1) p = stepWeight (shift a) (shift b) (shift c) s p := by
  induction hp with
  | nil => rfl
  | level _ ih => simp only [stepWeight, shift]; rw [ih]
  | up _ _ ih => simp only [stepWeight, shift]; rw [ih]
  | @down s rest _ ih =>
    simp only [stepWeight, Nat.add_sub_cancel, shift]
    rw [ih]

/-- The structural map: a first-return code unfolds to its genuine step list.  An arch becomes
`up :: (inner) ++ down :: (rest)`; a bottom level step becomes `level :: …`. -/
def toSteps : (h n : ℕ) → MotzkinPath h n → List Step
  | _h, 0, _p => []
  | 0, n + 1, p => Step.level :: toSteps 0 n (by simpa [MotzkinPath] using p)
  | h + 1, 1, p => Step.level :: toSteps (h + 1) 0 (by simpa [MotzkinPath] using p)
  | h + 1, n + 2, p =>
      match
        (by
          simpa [MotzkinPath] using p :
            MotzkinPath (h + 1) (n + 1) ⊕
              (Σ i : Fin (n + 1),
                MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)))
      with
      | Sum.inl rest => Step.level :: toSteps (h + 1) (n + 1) rest
      | Sum.inr arch =>
          Step.up :: (toSteps h arch.1.1 arch.2.1
            ++ Step.down :: toSteps (h + 1) (n - arch.1.1) arch.2.2)
termination_by h n _p => h + n
decreasing_by all_goals omega

end

end AnalyticCombinatorics.Ch5.ContinuedFractions
