import ClassicalThermodynamics.Models.IdealGas.Model
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Models.IdealGas

/-- Ideal-gas caloric data with constant positive molar heat capacity at
constant volume. -/
structure ConstantHeatCapacity (M : Model) where
  heatCapacityAtVolume : ℝ
  heatCapacityAtVolume_pos : 0 < heatCapacityAtVolume
  gasConstant_pos : 0 < M.gasConstant

/-- Molar heat capacity at constant pressure for a constant-heat-capacity
ideal gas. -/
def heatCapacityAtPressure (M : Model) (C : ConstantHeatCapacity M) : ℝ :=
  C.heatCapacityAtVolume + M.gasConstant

theorem heatCapacityAtPressure_pos (M : Model) (C : ConstantHeatCapacity M) :
    0 < heatCapacityAtPressure M C :=
  add_pos C.heatCapacityAtVolume_pos C.gasConstant_pos

/-- Heat-capacity ratio `γ = Cp/Cv`. -/
noncomputable def heatCapacityRatio (M : Model) (C : ConstantHeatCapacity M) : ℝ :=
  heatCapacityAtPressure M C / C.heatCapacityAtVolume

/-- Caloric internal-energy model for `n` moles. -/
def internalEnergy (M : Model) (C : ConstantHeatCapacity M) (n T : ℝ) : ℝ :=
  n * C.heatCapacityAtVolume * T

/-- Caloric enthalpy model for `n` moles. -/
def enthalpy (M : Model) (C : ConstantHeatCapacity M) (n T : ℝ) : ℝ :=
  n * heatCapacityAtPressure M C * T

/-- Dimensionless ideal-gas entropy potential relative to reference values.
Its endpoint difference is the physical entropy change in this model. -/
noncomputable def entropyPotential
    (M : Model) (C : ConstantHeatCapacity M) (n Tref Vref T V : ℝ) : ℝ :=
  n * C.heatCapacityAtVolume * Real.log (T / Tref) +
    n * M.gasConstant * Real.log (V / Vref)

/-- Ideal-gas entropy change for constant molar heat capacity at constant
volume. -/
noncomputable def entropyChange
    (M : Model) (C : ConstantHeatCapacity M) (n T₁ T₂ V₁ V₂ : ℝ) : ℝ :=
  n * C.heatCapacityAtVolume * Real.log (T₂ / T₁) +
    n * M.gasConstant * Real.log (V₂ / V₁)

theorem internalEnergy_change (M : Model) (C : ConstantHeatCapacity M)
    (n T₁ T₂ : ℝ) :
    internalEnergy M C n T₂ - internalEnergy M C n T₁ =
      n * C.heatCapacityAtVolume * (T₂ - T₁) := by
  unfold internalEnergy
  ring

theorem enthalpy_change (M : Model) (C : ConstantHeatCapacity M)
    (n T₁ T₂ : ℝ) :
    enthalpy M C n T₂ - enthalpy M C n T₁ =
      n * heatCapacityAtPressure M C * (T₂ - T₁) := by
  unfold enthalpy
  ring

theorem heatCapacityRatio_sub_one (M : Model) (C : ConstantHeatCapacity M) :
    heatCapacityRatio M C - 1 =
      M.gasConstant / C.heatCapacityAtVolume := by
  unfold heatCapacityRatio heatCapacityAtPressure
  have hCv : C.heatCapacityAtVolume ≠ 0 :=
    ne_of_gt C.heatCapacityAtVolume_pos
  field_simp
  ring

theorem entropyChange_eq_entropyPotential_difference
    (M : Model) (C : ConstantHeatCapacity M) (n Tref Vref T₁ T₂ V₁ V₂ : ℝ)
    (hTref : 0 < Tref) (hVref : 0 < Vref)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) :
    entropyChange M C n T₁ T₂ V₁ V₂ =
      entropyPotential M C n Tref Vref T₂ V₂ -
        entropyPotential M C n Tref Vref T₁ V₁ := by
  unfold entropyChange entropyPotential
  rw [Real.log_div hT₂.ne' hTref.ne', Real.log_div hT₁.ne' hTref.ne',
    Real.log_div hV₂.ne' hVref.ne', Real.log_div hV₁.ne' hVref.ne',
    Real.log_div hT₂.ne' hT₁.ne', Real.log_div hV₂.ne' hV₁.ne']
  ring

end ClassicalThermodynamics.Models.IdealGas
