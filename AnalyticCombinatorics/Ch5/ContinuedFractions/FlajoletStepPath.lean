import AnalyticCombinatorics.Ch5.ContinuedFractions.FlajoletPathBijection

/-!
# Ch5 §V — Flajolet's theorem on genuine step-list lattice paths (the bijection)

This completes the faithfulness upgrade begun in `FlajoletPathBijection.lean`: it proves the
weight-preserving bijection between the first-return-coded `MotzkinPath` type and genuine
lattice paths (`List Step` with the `Walk`/`ClosedMotzkin` validity), and assembles the capstone.

* `Walk_split` — drop a valid prefix (converse of `Walk_append`).
* `toSteps_surjective` — every closed lattice path is `toSteps` of some first-return code
  (the parse, via `first_passage` — the cycle lemma).
* `balanced_split_eq` — first-return uniqueness (two balanced prefixes + `down` agree).
* `toSteps_injective` — distinct codes give distinct step lists.
* `coeff_JFraction_eq_stepPathSum` — **Flajolet's theorem on real lattice paths**: the `z^n`
  coefficient of the bounded J-fraction is the weighted sum over all height-`≤h`, length-`n`
  closed Motzkin step paths, with the first-return decomposition now a *theorem*, not a definition.
-/

open scoped BigOperators PowerSeries

namespace AnalyticCombinatorics.Ch5.ContinuedFractions

noncomputable section

set_option maxHeartbeats 800000

variable {R : Type*} [CommRing R]

/-- Drop a valid prefix: if `l₁ ++ l₂` is a valid walk from `s`, then `l₂` is a valid walk from
`endLevel s l₁`.  (Converse of `Walk_append`.)  Induction on `l₁`. -/
lemma Walk_split {h : ℕ} : ∀ {s : ℕ} {l₁ l₂ : List Step},
    Walk h s (l₁ ++ l₂) → Walk h (endLevel s l₁) l₂ := by
  intro s l₁
  induction l₁ generalizing s with
  | nil => intro l₂ hw; simpa using hw
  | cons st rest ih =>
      intro l₂ hw
      cases st with
      | up =>
          rw [List.cons_append] at hw
          cases hw with
          | up hle sub =>
              have := ih sub
              simpa [endLevel_cons, Step.nextLevel] using this
      | down =>
          rw [List.cons_append] at hw
          cases hw with
          | down sub =>
              have := ih sub
              simpa [endLevel_cons, Step.nextLevel, Nat.add_sub_cancel] using this
      | level =>
          rw [List.cons_append] at hw
          cases hw with
          | level sub =>
              have := ih sub
              simpa [endLevel_cons, Step.nextLevel] using this

/-- No down step from the floor: a valid walk from level `0` cannot start with `down`. -/
lemma not_walk_zero_down {h : ℕ} {rest : List Step} : ¬ Walk h 0 (Step.down :: rest) := by
  intro hw; cases hw

/-- **Surjectivity (the parse).**  Every closed lattice path of height `≤ h`, length `n`, is the
step list of some first-return code.  Strong induction on length; the `up` case invokes the
first-passage decomposition. -/
lemma toSteps_surjective : ∀ (n h : ℕ) (p : List Step),
    Walk h 0 p → endLevel 0 p = 0 → p.length = n →
    ∃ q : MotzkinPath h n, toSteps h n q = p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro h p hw hend hlen
    cases p with
    | nil =>
        -- n = 0, code = PUnit
        have hn0 : n = 0 := by simpa using hlen.symm
        subst hn0
        exact ⟨(by rw [MotzkinPath.eq_1]; exact PUnit.unit), by simp [toSteps]⟩
    | cons st rest =>
        cases st with
        | down => exact absurd hw not_walk_zero_down
        | level =>
            -- p = level :: rest ; rest is a closed path of length n-1
            have hwrest : Walk h 0 rest := by cases hw with | level sub => exact sub
            have hendrest : endLevel 0 rest = 0 := by
              simpa [endLevel_cons, Step.nextLevel] using hend
            have hn : rest.length + 1 = n := by
              have h := hlen; simp only [List.length_cons] at h; omega
            cases h with
            | zero =>
                subst hn
                obtain ⟨q', hq'⟩ := IH rest.length (by omega) 0 rest hwrest hendrest rfl
                exact ⟨(MotzkinPath.eq_2 rest.length).mpr q', by simp [toSteps, hq']⟩
            | succ h' =>
                by_cases hrl : rest.length = 0
                · have hn1 : n = 1 := by omega
                  subst hn1
                  obtain ⟨q', hq'⟩ := IH 0 (by omega) (h' + 1) rest hwrest hendrest hrl
                  exact ⟨(MotzkinPath.eq_3 h').mpr q', by simp [toSteps, hq']⟩
                · obtain ⟨k, hk⟩ : ∃ k, rest.length = k + 1 :=
                    Nat.exists_eq_succ_of_ne_zero hrl
                  have hn2 : n = k + 2 := by omega
                  subst hn2
                  obtain ⟨q', hq'⟩ := IH (k + 1) (by omega) (h' + 1) rest hwrest hendrest hk
                  exact ⟨(MotzkinPath.eq_4 h' k).mpr (Sum.inl q'), by simp [toSteps, hq']⟩
        | up =>
            -- p = up :: rest ; h = h'+1, rest from level 1 returns to 0
            cases hw with
            | up hle sub =>
            obtain ⟨h', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show h ≠ 0 by omega)
            -- sub : Walk (h'+1) 1 rest
            have hendrest : endLevel 1 rest ≤ 1 - 1 := by
              have h2 : endLevel 0 (Step.up :: rest) = 0 := hend
              simp only [endLevel_cons, Step.nextLevel, Nat.zero_add] at h2
              omega
            obtain ⟨M, B, hsplit, hWM, hEM, hWB, hEB⟩ :=
              first_passage rest.length rest 1 rfl (le_refl 1) sub hendrest
            have hEB0 : endLevel 0 B = 0 := by
              have h3 : endLevel 1 rest = 0 := by
                have h2 : endLevel 0 (Step.up :: rest) = 0 := hend
                simpa [endLevel_cons, Step.nextLevel] using h2
              simpa [h3] using hEB
            have hn : rest.length + 1 = n := by
              have h := hlen; simp only [List.length_cons] at h; omega
            -- lengths: rest = M ++ down :: B ⟹ rest.length = M.length + B.length + 1
            have hlenrest : rest.length = M.length + B.length + 1 := by
              rw [hsplit]; simp only [List.length_append, List.length_cons]; omega
            have hMlt : M.length < n := by omega
            have hBlt : B.length < n := by omega
            obtain ⟨innerCode, hinner⟩ :=
              IH M.length hMlt h' M (by simpa using hWM) (by simpa using hEM) rfl
            -- obtain restCode already at the eq_4 index (M.length+B.length) - M.length: no cast
            obtain ⟨restCode, hrestc⟩ :=
              IH (M.length + B.length - M.length) (by omega) (h' + 1) B hWB hEB0 (by omega)
            -- assemble arch code via eq_4 ∘ Sum.inr ; n = M.length+B.length+2
            have hnm : n = M.length + B.length + 2 := by omega
            subst hnm
            refine ⟨(MotzkinPath.eq_4 h' (M.length + B.length)).mpr
              (Sum.inr ⟨⟨M.length, by omega⟩, innerCode, restCode⟩), ?_⟩
            rw [hsplit]
            simp [toSteps, hinner, hrestc]

/-- First-return uniqueness: two balanced valid prefixes each followed by a `down` must agree. -/
lemma balanced_split_eq {h : ℕ} : ∀ {A₁ A₂ B₁ B₂ : List Step},
    Walk h 0 A₁ → endLevel 0 A₁ = 0 → Walk h 0 A₂ → endLevel 0 A₂ = 0 →
    A₁ ++ Step.down :: B₁ = A₂ ++ Step.down :: B₂ → A₁ = A₂ ∧ B₁ = B₂ := by
  intro A₁ A₂ B₁ B₂ hw1 he1 hw2 he2 heq
  rcases List.append_eq_append_iff.mp heq with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
  · rcases c with _ | ⟨st, c'⟩
    · refine ⟨by simpa using hc1.symm, by simpa using hc2⟩
    · simp only [List.cons_append] at hc2
      obtain ⟨rfl, _⟩ := List.cons.inj hc2
      rw [hc1] at hw2
      have hsp := Walk_split hw2
      rw [he1] at hsp
      exact absurd hsp not_walk_zero_down
  · rcases c with _ | ⟨st, c'⟩
    · refine ⟨by simpa using hc1, by simpa using hc2.symm⟩
    · simp only [List.cons_append] at hc2
      obtain ⟨rfl, _⟩ := List.cons.inj hc2
      rw [hc1] at hw1
      have hsp := Walk_split hw1
      rw [he2] at hsp
      exact absurd hsp not_walk_zero_down

/-- **Injectivity.**  Distinct first-return codes give distinct step lists.  Strong induction on
length: `0`/`1` cases by `Subsingleton`; the `eq_2`/`eq_4` destructure of `q₁,q₂` via the
`simp [toSteps]` constructor equations; the arch case by `balanced_split_eq` + `IH`. -/
lemma toSteps_injective : ∀ (n h : ℕ) (q₁ q₂ : MotzkinPath h n),
    toSteps h n q₁ = toSteps h n q₂ → q₁ = q₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro h q₁ q₂ heq
  rcases n with _ | m
  · have hs : Subsingleton (MotzkinPath h 0) := by rw [MotzkinPath.eq_1]; infer_instance
    exact Subsingleton.elim q₁ q₂
  · rcases h with _ | h'
    · -- h = 0, n = m+1
      have h1 : q₁ = (MotzkinPath.eq_2 m).mpr ((MotzkinPath.eq_2 m).mp q₁) := by simp
      have h2 : q₂ = (MotzkinPath.eq_2 m).mpr ((MotzkinPath.eq_2 m).mp q₂) := by simp
      have hmp : (MotzkinPath.eq_2 m).mp q₁ = (MotzkinPath.eq_2 m).mp q₂ := by
        apply IH m (by omega) 0
        have hd1 : toSteps 0 (m + 1) q₁
            = Step.level :: toSteps 0 m ((MotzkinPath.eq_2 m).mp q₁) := by
          conv_lhs => rw [h1]
          simp [toSteps]
        have hd2 : toSteps 0 (m + 1) q₂
            = Step.level :: toSteps 0 m ((MotzkinPath.eq_2 m).mp q₂) := by
          conv_lhs => rw [h2]
          simp [toSteps]
        rw [hd1, hd2] at heq
        simpa using heq
      rw [h1, h2, hmp]
    · rcases m with _ | k
      · have hs : Subsingleton (MotzkinPath (h' + 1) 1) := by
          rw [MotzkinPath.eq_3, MotzkinPath.eq_1]; infer_instance
        exact Subsingleton.elim q₁ q₂
      · -- h'+1, n = k+2
        have h1 : q₁ = (MotzkinPath.eq_4 h' k).mpr ((MotzkinPath.eq_4 h' k).mp q₁) := by simp
        have h2 : q₂ = (MotzkinPath.eq_4 h' k).mpr ((MotzkinPath.eq_4 h' k).mp q₂) := by simp
        have hmp : (MotzkinPath.eq_4 h' k).mp q₁ = (MotzkinPath.eq_4 h' k).mp q₂ := by
          rcases hsv1 : (MotzkinPath.eq_4 h' k).mp q₁ with r₁ | a₁ <;>
            rcases hsv2 : (MotzkinPath.eq_4 h' k).mp q₂ with r₂ | a₂
          · -- inl, inl
            have hd1 : toSteps (h' + 1) (k + 2) q₁
                = Step.level :: toSteps (h' + 1) (k + 1) r₁ := by
              conv_lhs => rw [h1, hsv1]
              simp [toSteps]
            have hd2 : toSteps (h' + 1) (k + 2) q₂
                = Step.level :: toSteps (h' + 1) (k + 1) r₂ := by
              conv_lhs => rw [h2, hsv2]
              simp [toSteps]
            rw [hd1, hd2] at heq
            rw [IH (k + 1) (by omega) (h' + 1) r₁ r₂ (by simpa using heq)]
          · -- inl, inr : impossible
            exfalso
            have hd1 : toSteps (h' + 1) (k + 2) q₁
                = Step.level :: toSteps (h' + 1) (k + 1) r₁ := by
              conv_lhs => rw [h1, hsv1]
              simp [toSteps]
            have hd2 : toSteps (h' + 1) (k + 2) q₂
                = Step.up :: (toSteps h' a₂.1.1 a₂.2.1
                  ++ Step.down :: toSteps (h' + 1) (k - a₂.1.1) a₂.2.2) := by
              conv_lhs => rw [h2, hsv2]
              simp [toSteps]
            rw [hd1, hd2] at heq; simp at heq
          · -- inr, inl : impossible
            exfalso
            have hd1 : toSteps (h' + 1) (k + 2) q₁
                = Step.up :: (toSteps h' a₁.1.1 a₁.2.1
                  ++ Step.down :: toSteps (h' + 1) (k - a₁.1.1) a₁.2.2) := by
              conv_lhs => rw [h1, hsv1]
              simp [toSteps]
            have hd2 : toSteps (h' + 1) (k + 2) q₂
                = Step.level :: toSteps (h' + 1) (k + 1) r₂ := by
              conv_lhs => rw [h2, hsv2]
              simp [toSteps]
            rw [hd1, hd2] at heq; simp at heq
          · -- inr, inr : arch
            obtain ⟨i₁, inner₁, rest₁⟩ := a₁
            obtain ⟨i₂, inner₂, rest₂⟩ := a₂
            have hd1 : toSteps (h' + 1) (k + 2) q₁
                = Step.up :: (toSteps h' i₁.1 inner₁
                  ++ Step.down :: toSteps (h' + 1) (k - i₁.1) rest₁) := by
              conv_lhs => rw [h1, hsv1]
              simp [toSteps]
            have hd2 : toSteps (h' + 1) (k + 2) q₂
                = Step.up :: (toSteps h' i₂.1 inner₂
                  ++ Step.down :: toSteps (h' + 1) (k - i₂.1) rest₂) := by
              conv_lhs => rw [h2, hsv2]
              simp [toSteps]
            rw [hd1, hd2] at heq
            have heq' : toSteps h' i₁.1 inner₁ ++ Step.down :: toSteps (h' + 1) (k - i₁.1) rest₁
                = toSteps h' i₂.1 inner₂ ++ Step.down :: toSteps (h' + 1) (k - i₂.1) rest₂ := by
              simpa using heq
            obtain ⟨hMeq, hBeq⟩ := balanced_split_eq (toSteps_walk h' i₁.1 inner₁)
              (endLevel_toSteps h' i₁.1 inner₁ 0) (toSteps_walk h' i₂.1 inner₂)
              (endLevel_toSteps h' i₂.1 inner₂ 0) heq'
            have hi : i₁.1 = i₂.1 := by
              have hl := congrArg List.length hMeq
              rwa [toSteps_length, toSteps_length] at hl
            have hii : i₁ = i₂ := Fin.ext hi
            subst hii
            have hin : inner₁ = inner₂ := IH i₁.1 (by omega) h' inner₁ inner₂ hMeq
            have hre : rest₁ = rest₂ := IH (k - i₁.1) (by omega) (h' + 1) rest₁ rest₂ hBeq
            rw [hin, hre]
        rw [h1, h2, hmp]

/-- The genuine lattice-path finset: images of the codes under `toSteps`. -/
def closedMotzkinFinset (h n : ℕ) : Finset (List Step) :=
  (Finset.univ : Finset (MotzkinPath h n)).image (toSteps h n)

/-- Membership = being a genuine closed lattice path (⊇ is surjectivity, ⊆ is structural validity). -/
lemma mem_closedMotzkinFinset {h n : ℕ} {p : List Step} :
    p ∈ closedMotzkinFinset h n ↔ ClosedMotzkin h n p := by
  constructor
  · rintro hp
    rw [closedMotzkinFinset, Finset.mem_image] at hp
    obtain ⟨q, _, rfl⟩ := hp
    exact ⟨toSteps_walk h n q, endLevel_toSteps h n q 0, toSteps_length h n q⟩
  · rintro ⟨hw, hend, hlen⟩
    rw [closedMotzkinFinset, Finset.mem_image]
    obtain ⟨q, hq⟩ := toSteps_surjective n h p hw hend hlen
    exact ⟨q, Finset.mem_univ _, hq⟩

/-- **Flajolet's theorem on genuine lattice paths.**  The `z^n` coefficient of the bounded
J-fraction is the weighted sum over all height-`≤h`, length-`n` closed Motzkin step paths. -/
theorem coeff_JFraction_eq_stepPathSum (h n : ℕ) (a b c : ℕ → R) :
    PowerSeries.coeff (R := R) n (JFraction h a b c)
      = ∑ p ∈ closedMotzkinFinset h n, stepWeight a b c 0 p := by
  rw [PathSum.coeff_JFraction_eq_pathSum, WpathSum]
  rw [closedMotzkinFinset,
    Finset.sum_image (fun q₁ _ q₂ _ hq => toSteps_injective n h q₁ q₂ hq)]
  exact Finset.sum_congr rfl (fun q _ => (stepWeight_toSteps h n q a b c).symm)

end

end AnalyticCombinatorics.Ch5.ContinuedFractions
