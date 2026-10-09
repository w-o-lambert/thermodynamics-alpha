import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import ClassicalThermodynamics.Math.Calculus.MixedPartials

namespace ClassicalThermodynamics.Math.Calculus

/-- Schwarz symmetry obtained from actual `C²` regularity over the reals. -/
theorem schwarz_of_contDiffAt_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    IsSymmSndFDerivAt ℝ f x := by
  exact hf.isSymmSndFDerivAt (by simp)

theorem second_fderiv_apply_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x v w : E} (hf : ContDiffAt ℝ 2 f x) :
    (fderiv ℝ (fderiv ℝ f) x) v w = (fderiv ℝ (fderiv ℝ f) x) w v := by
  exact schwarz_of_contDiffAt_two hf v w

end ClassicalThermodynamics.Math.Calculus
