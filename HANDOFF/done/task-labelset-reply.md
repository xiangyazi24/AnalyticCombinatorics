done

Diff summary:
- Added `labelSetCount`.
- Proved `labelSetCount_div_factorial_eq_partial_exp_coeff`.
- The proof distributes `/ n!` over the finite sum, rewrites each term through `labelPow_count_div_factorial_eq_coeff_pow`, then closes the factorial-denominator rearrangement with `field_simp`.

Verification:
- `lake build` passes: 2764 jobs, 0 errors.

Codex: idle — task done
