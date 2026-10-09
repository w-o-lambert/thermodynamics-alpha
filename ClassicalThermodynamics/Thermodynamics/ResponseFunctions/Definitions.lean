import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
namespace ClassicalThermodynamics.Thermodynamics.ResponseFunctions

noncomputable def ThermalExpansion (V dVdT : ℝ) : ℝ := dVdT / V
noncomputable def IsothermalCompressibility (V dVdP : ℝ) : ℝ := -dVdP / V

def HeatCapacityDifferenceIdentity (Cp Cv T V alpha kappa : ℝ) : Prop :=
  Cp - Cv = T * V * alpha^2 / kappa

theorem heatCapacityDifference_nonnegative
    {Cp Cv T V alpha kappa : ℝ}
    (h : HeatCapacityDifferenceIdentity Cp Cv T V alpha kappa)
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hk : 0 < kappa) : 0 ≤ Cp - Cv := by
  rw [h]; positivity
end ClassicalThermodynamics.Thermodynamics.ResponseFunctions
