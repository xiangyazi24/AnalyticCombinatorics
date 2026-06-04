import Mathlib
import AnalyticCombinatorics.Ch7.SingularityApp.FussCatalan

/-!
# Named Fuss–Catalan instances (p-ary trees), F&S Ch VII

Concrete specializations of `fussCatalan_isEquivalent` to the classical small `p`-ary tree families:
ternary already lives in `TernaryTrees`; here we record quaternary (`p = 4`), quinary (`p = 5`) and
senary (`p = 6`), with their explicit growth bases `p^p/(p-1)^(p-1)`.

Each asymptotic is an immediate instance of the general theorem; the growth-base values are by
`norm_num`. (Opus-authored increment; no codex.)
-/

open Filter Asymptotics

namespace AnalyticCombinatorics
namespace Ch7
namespace SingularityApp

/-- Quaternary (4-ary) trees: `fussCatalan 4 n ~ C₄ · (256/27)^n · n^(-3/2)`. -/
theorem fussCatalan_four_isEquivalent :
    (fun n : ℕ => (_root_.fussCatalan 4 n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        _root_.fussCatalanConst 4 * _root_.fussCatalanBase 4 ^ n *
          ((n : ℝ) ^ (-(3 / 2) : ℝ))) := by
  simpa [_root_.fussCatalanConst, _root_.fussCatalanBase] using
    _root_.fussCatalan_isEquivalent 4 (by norm_num)

/-- Growth base of quaternary trees: `4^4/3^3 = 256/27`. -/
lemma fussCatalanBase_four : _root_.fussCatalanBase 4 = 256 / 27 := by
  norm_num [_root_.fussCatalanBase]

/-- Quinary (5-ary) trees: `fussCatalan 5 n ~ C₅ · (3125/256)^n · n^(-3/2)`. -/
theorem fussCatalan_five_isEquivalent :
    (fun n : ℕ => (_root_.fussCatalan 5 n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        _root_.fussCatalanConst 5 * _root_.fussCatalanBase 5 ^ n *
          ((n : ℝ) ^ (-(3 / 2) : ℝ))) := by
  simpa [_root_.fussCatalanConst, _root_.fussCatalanBase] using
    _root_.fussCatalan_isEquivalent 5 (by norm_num)

/-- Growth base of quinary trees: `5^5/4^4 = 3125/256`. -/
lemma fussCatalanBase_five : _root_.fussCatalanBase 5 = 3125 / 256 := by
  norm_num [_root_.fussCatalanBase]

/-- Senary (6-ary) trees: `fussCatalan 6 n ~ C₆ · (6^6/5^5)^n · n^(-3/2)`. -/
theorem fussCatalan_six_isEquivalent :
    (fun n : ℕ => (_root_.fussCatalan 6 n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        _root_.fussCatalanConst 6 * _root_.fussCatalanBase 6 ^ n *
          ((n : ℝ) ^ (-(3 / 2) : ℝ))) := by
  simpa [_root_.fussCatalanConst, _root_.fussCatalanBase] using
    _root_.fussCatalan_isEquivalent 6 (by norm_num)

/-- Growth base of senary trees: `6^6/5^5 = 46656/3125`. -/
lemma fussCatalanBase_six : _root_.fussCatalanBase 6 = 46656 / 3125 := by
  norm_num [_root_.fussCatalanBase]

end SingularityApp
end Ch7
end AnalyticCombinatorics
