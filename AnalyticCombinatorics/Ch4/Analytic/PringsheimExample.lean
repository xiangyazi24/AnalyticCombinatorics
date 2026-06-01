import AnalyticCombinatorics.Ch4.Analytic.Pringsheim

open Filter
open scoped NNReal ENNReal Topology

noncomputable section

/-- The all-ones ordinary generating function has radius of convergence `1`. -/
theorem geometric_radius_eq_one :
    (FormalMultilinearSeries.ofScalars ℂ (fun _ : ℕ => (1 : ℂ))).radius =
      (1 : ℝ≥0∞) := by
  simpa using
    (FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto ℂ
      (fun _ : ℕ => (1 : ℂ)) (r := (1 : ℝ≥0)) one_ne_zero (by simp))

/-- Pringsheim applied to the all-ones class: its generating function is singular at `1`. -/
theorem geometric_singularity_at_one :
    ¬ AnalyticAt ℂ
      (FormalMultilinearSeries.ofScalars ℂ (fun _ : ℕ => (1 : ℂ))).sum
      (1 : ℂ) := by
  simpa using
    (pringsheim_not_analyticAt (fun _ : ℕ => (1 : ℝ≥0))
      (R := (1 : ℝ≥0)) zero_lt_one geometric_radius_eq_one)

end
