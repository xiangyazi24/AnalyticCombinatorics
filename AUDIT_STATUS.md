# AUDIT_STATUS — C-group fidelity spot-checks

Tracking statement-fidelity verdicts for headline theorems, per formalization-playbook
Phase 3 (Group C semantic review). The old tree (archive/impostor-2026-05) was a whole-repo
IMPOSTOR; every "FAITHFUL" claim in the rebuilt tree must be spot-checked against F&S.

Verdict legend: FAITHFUL / CONDITIONAL-honest / FRAGMENT / IMPOSTOR.

## Checked 2026-06-03

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `catalan_isEquivalent_complex_sqrt_mul_nat` | — | `catalan n ~ 4^n/(√(πn)·n)` = 4^n/(√π·n^{3/2}) | FAITHFUL |
| `catalan_isEquivalent_real_rpow` | — | `catalan n ~ 4^n/(√π·n^{3/2})` | FAITHFUL |
| `fib_isEquivalent_real` | — | `fib(n+1) ~ (φ/(φ-ψ))·φ^n` = (φ/√5)·φ^n | FAITHFUL |
| `transfer_theorem_re_alpha_gt_one` | VI.3 | Δ-domain analytic + singular expansion `f ~ C(1-z)^{-α}` ⟹ `[z^n]f ~ C·n^{α-1}/Γ(α)` (Re α>1) | FAITHFUL — genuine analytic hypotheses, proof subtracts principal part + bounds remainder o(n^{α.re-1}) |
| `CombClass.egf_bell` | II | `posInt.set.egf = exp(exp-1)` (Bell EGF e^{e^z-1}) | FAITHFUL |
| `CombClass.egf_surjections` | II.3 | `lseq.egf·(2-e^z) = 1` (surjection EGF 1/(2-e^z)) | FAITHFUL |
| `exp_coeff_isEquivalent_saddle` | VIII | exp coeff ~ saddleScale (= e^n/(n^n√(2πn))) | FAITHFUL, unconditional |
| `coeff_isEquivalent_saddle` (HAdmissible) | VIII.4 | given `HAdmissible f p`, `p.coeff n ~ saddleScale` | CONDITIONAL-honest — general transfer, no concrete instance yet |

Conclusion so far: the rebuilt tree's headline asymptotics are genuine `IsEquivalent`
statements with correct constants — not the trivially-true projections of the old impostor
tree. Continue spot-checks chapter by chapter as coverage grows.
