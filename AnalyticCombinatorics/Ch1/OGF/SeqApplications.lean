import AnalyticCombinatorics.Ch1.OGF.SequenceInverse
import AnalyticCombinatorics.Ch1.OGF.ProductPower
import AnalyticCombinatorics.Ch1.OGF.SeqFormula

/-!
# Ch1 §I.3 — Applications of the sequence construction

Flajolet & Sedgewick, Part A, Chapter I, §I.3, applying the general transfer
`SEQ(C)(z) = 1/(1 - C(z))` (`ogf_seq_mul`):

* `counts_seq_alphabet` / `ogf_seq_alphabet` — **words over a finite alphabet**:
  `SEQ` of an `a`-letter alphabet enumerates all words; there are `a^n` of length
  `n`, with OGF `1/(1 - a z)`.
* `ogf_seq_posInt` — **compositions revisited**: the special case `C = ℙ`
  recovers `(seq ℙ)(z)·(1 - ℙ(z)) = 1` as an instance of the general theorem
  (cf. the bespoke proof in `SeqFormula.lean`).
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- **Number of words** (F&S §I.3): there are `a^n` words of length `n` over an
`a`-letter alphabet, i.e. `(SEQ (alphabet a))ₙ = a^n`. -/
theorem counts_seq_alphabet (a n : ℕ) :
    (CombClass.alphabet a).seq.counts n = a ^ n := by
  induction n with
  | zero => rw [counts_seq_zero, pow_zero]
  | succ n ih =>
    rw [counts_seq_succ, Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp [CombClass.counts_alphabet, ih, pow_succ']
    · intro k _ hk
      have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.eq_of_val_eq h)
      rw [CombClass.counts_alphabet, if_neg (by omega), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **OGF of words** (F&S §I.3): `SEQ(alphabet a)(z)·(1 - a z) = 1`, i.e. the OGF
of all words over an `a`-letter alphabet is `1/(1 - a z)`. -/
theorem ogf_seq_alphabet (a : ℕ) :
    (CombClass.alphabet a).seq.ogf * (1 - (a : ℕ) • X) = 1 := by
  have h := CombClass.ogf_seq_mul (C := CombClass.alphabet a)
    (by simp [CombClass.counts_alphabet])
  rwa [CombClass.ogf_alphabet] at h

/-- **Compositions as a special case** (F&S §I.3): `(seq ℙ)(z)·(1 - ℙ(z)) = 1`
follows directly from the general sequence transfer, since `ℙ₀ = ∅`. -/
theorem ogf_seq_posInt :
    CombClass.posInt.seq.ogf * (1 - CombClass.posInt.ogf) = 1 :=
  CombClass.ogf_seq_mul (by simp [CombClass.counts_posInt])

end AnalyticCombinatorics.Ch1
