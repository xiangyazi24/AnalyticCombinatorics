import AnalyticCombinatorics.Ch3.BGF.Variance
import AnalyticCombinatorics.Ch3.BGF.BinaryWords

/-!
# Ch3 -- Mean and variance for ones in binary words

For length-`n` binary words, the number of ones has the binomial distribution
`Bin(n, 1/2)`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

private lemma counts_binaryWords (n : ℕ) :
    ParamClass.binaryWords.toCombClass.counts n = 2 ^ n := by
  rw [CombClass.counts, ParamClass.binaryWords]
  simp [Fintype.card_bool]

private lemma coeff_factorialMoment1_binaryWords (n : ℕ) :
    PowerSeries.coeff n (factorialMoment1 ParamClass.binaryWords.bgf) =
      ((n : ℚ) / 2) * (2 : ℚ) ^ n := by
  rcases n with _ | n
  · simp [factorialMoment1, evalU, uDeriv, ParamClass.bgf, paramPoly_binaryWords]
  · simp [factorialMoment1, evalU, uDeriv, ParamClass.bgf, paramPoly_binaryWords,
      Polynomial.derivative_pow, Polynomial.eval_pow]
    ring_nf

private lemma coeff_rawMoment2_binaryWords (n : ℕ) :
    PowerSeries.coeff n (rawMoment2 ParamClass.binaryWords.bgf) =
      ((n : ℚ) * ((n : ℚ) + 1) / 4) * (2 : ℚ) ^ n := by
  rcases n with _ | n
  · rw [ParamClass.coeff_rawMoment2]
    simp [ParamClass.binaryWords]
  rcases n with _ | n
  · simp [rawMoment2, evalU, uDeriv, ParamClass.bgf, paramPoly_binaryWords,
      Polynomial.derivative_pow]
    norm_num
  · simp [rawMoment2, evalU, uDeriv, ParamClass.bgf, paramPoly_binaryWords,
      Polynomial.derivative_pow, Polynomial.eval_pow]
    ring_nf

private lemma mean_binaryWords_all (n : ℕ) :
    ParamClass.binaryWords.mean n = (n : ℚ) / 2 := by
  rw [ParamClass.mean]
  rw [coeff_factorialMoment1_binaryWords n, counts_binaryWords]
  norm_num [Nat.cast_pow]

theorem ParamClass.mean_binaryWords {n : ℕ} (hn : 1 ≤ n) :
    ParamClass.binaryWords.mean n = (n : ℚ) / 2 := by
  rcases n with _ | n
  · omega
  · exact mean_binaryWords_all (n + 1)

theorem ParamClass.variance_binaryWords {n : ℕ} :
    ParamClass.binaryWords.variance n = (n : ℚ) / 4 := by
  rw [ParamClass.variance]
  rw [coeff_rawMoment2_binaryWords n, mean_binaryWords_all n, counts_binaryWords]
  norm_num [Nat.cast_pow]
  ring

end AnalyticCombinatorics.Ch1
