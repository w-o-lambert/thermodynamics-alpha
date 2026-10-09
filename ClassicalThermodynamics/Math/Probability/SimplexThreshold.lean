import Mathlib.Basic.Real.Basic
namespace ClassicalThermodynamics.Math.Probability
/-- Expected-count expression used when a uniformly sampled simplex coordinate
exceeds a threshold h. The probabilistic derivation is deferred; this exact
finite-N expression is the algebraic object appearing in Qiang-Luo-Zwicker. -/
noncomputable def simplexThresholdCount (N : ℕ) (h : ℝ) : ℝ :=
  N * (1 - h)^(N - 1)
@[simp] theorem simplexThresholdCount_zero (N : ℕ) :
    simplexThresholdCount N 0 = N := by simp [simplexThresholdCount]
end ClassicalThermodynamics.Math.Probability
