import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
namespace ClassicalThermodynamics.Thermodynamics.Relations
/-- van 't Hoff differential relation d(log K)/dT = ΔH/(R T²). -/
def VanTHoffAt (K deltaH : ℝ → ℝ) (R T : ℝ) : Prop :=
  K T ≠ 0 ∧ R ≠ 0 ∧ T ≠ 0 ∧
    HasDerivAt (fun t => Real.log (K t)) (deltaH T / (R * T^2)) T
end ClassicalThermodynamics.Thermodynamics.Relations
