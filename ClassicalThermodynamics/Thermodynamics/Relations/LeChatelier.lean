import ClassicalThermodynamics.Thermodynamics.Stability.Convexity
import Mathlib.Basic.Real.Basic
namespace ClassicalThermodynamics.Thermodynamics.Relations
/-- Minimal response formulation: restoring response has sign opposite to a perturbation. -/
def RestoringResponse (perturbation response : ℝ) : Prop := perturbation * response ≤ 0
end ClassicalThermodynamics.Thermodynamics.Relations
