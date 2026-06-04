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

### Checked 2026-06-03 (symbolic method + moments)

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `CombClass.ogf_prod` | I.1 | `(C×D).ogf = C.ogf·D.ogf` | FAITHFUL |
| `CombClass.ogf_sum` | I.1 | `(C+D).ogf = C.ogf+D.ogf` | FAITHFUL |
| `CombClass.ogf_seq_mul` | I.2 | `C.seq.ogf·(1-C.ogf)=1` (quasi-inverse SEQ) | FAITHFUL |
| `CombClass.ogf_mset` | I.2 | `MSET(C).ogf = ∏_i ∑_k multichoose(c_i,k)X^{ik}` | FAITHFUL |
| `CombClass.ogf_partitions` | I.3 | `∏_i ∑_j X^{(i+1)j}` (= ∏ 1/(1-X^{i+1}), Euler) | FAITHFUL |
| `CombClass.ogf_pset` | I.2 | `PSET(C).ogf = ∏_i ∑_k choose(c_i,k)X^{ik}` | FAITHFUL |
| `ParamClass.mean_eq` | III | `mean = (Σ param)/count` | FAITHFUL |
| `ParamClass.variance_eq` | III | `variance = (Σ param²)/count − mean²` | FAITHFUL |

### Checked 2026-06-03 (Ch2 EGF core)

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `CombClass.egf_lprod` | II.1 | `(A⋆B).egf = A.egf·B.egf` (labelled product) | FAITHFUL |
| `CombClass.egf_set` | II.2 | `SET(C).egf = exp(C.egf)` (C.counts 0 = 0) | FAITHFUL |
| `CombClass.egf_lseq` | II.2 | `SEQ(C).egf·(1-C.egf)=1` | FAITHFUL |
| `CombClass.egf_lcyc_ode` | II.2 | `d/dX CYC(C).egf = C.egf'·SEQ(C).egf` (CYC = log 1/(1-C)) | FAITHFUL |

Conclusion so far: spot-checks across ALL existing chapters (Ch1 OGF, Ch2 EGF, Ch3 BGF,
Ch4 complex+singularity, Ch8 saddle) — every core transfer rule and payoff theorem is a genuine,
correctly-constanted statement. The rebuilt tree is honest, unlike the old whole-repo impostor.
Continue spot-checks chapter by chapter as coverage grows.
