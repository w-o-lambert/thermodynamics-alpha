import Mathlib.Basic.Real.Basic
namespace ClassicalThermodynamics.Models.RegularMixture
/-- Symmetric binary regular-solution excess Gibbs energy. -/
noncomputable def excessGibbs (interaction x : ℝ) : ℝ := interaction * x * (1-x)
end ClassicalThermodynamics.Models.RegularMixture
