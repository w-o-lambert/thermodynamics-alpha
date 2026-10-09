import ClassicalThermodynamics.Thermodynamics.Differentials.Gibbs
import Mathlib.Analysis.Calculus.Deriv.Basic
namespace ClassicalThermodynamics.Thermodynamics.Relations
/-- Gibbs-Helmholtz in derivative form, parameterized by enthalpy. -/
def GibbsHelmholtzAt (G H : ℝ → ℝ) (T : ℝ) : Prop :=
  T ≠ 0 ∧ HasDerivAt (fun t => G t / t) (- H T / T^2) T
end ClassicalThermodynamics.Thermodynamics.Relations
