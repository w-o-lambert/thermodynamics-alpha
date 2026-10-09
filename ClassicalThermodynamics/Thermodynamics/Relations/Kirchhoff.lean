import Mathlib.Analysis.Calculus.Deriv.Basic
namespace ClassicalThermodynamics.Thermodynamics.Relations
/-- Kirchhoff reaction-enthalpy relation d(ΔH)/dT = ΔCp. -/
def KirchhoffAt (deltaH deltaCp : ℝ → ℝ) (T : ℝ) : Prop := HasDerivAt deltaH (deltaCp T) T
end ClassicalThermodynamics.Thermodynamics.Relations
