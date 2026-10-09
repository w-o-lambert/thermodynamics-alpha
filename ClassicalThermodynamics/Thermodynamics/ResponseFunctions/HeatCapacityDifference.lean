import ClassicalThermodynamics.Thermodynamics.ResponseFunctions.Definitions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF
namespace ClassicalThermodynamics.Thermodynamics.ResponseFunctions

/-- Algebraic chain-rule data for entropy S(T,V(T,P)) along a constant-pressure path. -/
structure EntropyResponseData where
  temperature : ℝ
  volume : ℝ
  dS_dT_atV : ℝ
  dS_dV_atT : ℝ
  dV_dT_atP : ℝ
  dV_dP_atT : ℝ

noncomputable def heatCapacityAtVolume (D : EntropyResponseData) : ℝ :=
  D.temperature * D.dS_dT_atV

noncomputable def heatCapacityAtPressure (D : EntropyResponseData) : ℝ :=
  D.temperature * (D.dS_dT_atV + D.dS_dV_atT * D.dV_dT_atP)

noncomputable def thermalExpansion (D : EntropyResponseData) : ℝ :=
  D.dV_dT_atP / D.volume

noncomputable def isothermalCompressibility (D : EntropyResponseData) : ℝ :=
  -D.dV_dP_atT / D.volume

/-- First reduction: Cp-Cv = T (∂S/∂V)_T (∂V/∂T)_P. -/
lemma heatCapacityDifference_chainRule (D : EntropyResponseData) :
    heatCapacityAtPressure D - heatCapacityAtVolume D =
      D.temperature * D.dS_dV_atT * D.dV_dT_atP := by
  unfold heatCapacityAtPressure heatCapacityAtVolume
  ring

/-- Maxwell substitution (∂S/∂V)_T = (∂P/∂T)_V. -/
lemma heatCapacityDifference_of_maxwell
    (D : EntropyResponseData) (dP_dT_atV : ℝ)
    (hMaxwell : D.dS_dV_atT = dP_dT_atV) :
    heatCapacityAtPressure D - heatCapacityAtVolume D =
      D.temperature * dP_dT_atV * D.dV_dT_atP := by
  rw [heatCapacityDifference_chainRule, hMaxwell]

/-- Cyclic inverse-response relation in denominator-cleared form:
(∂P/∂T)_V (-∂V/∂P)_T = (∂V/∂T)_P. -/
def EquationOfStateResponseRelation
    (dP_dT_atV dV_dP_atT dV_dT_atP : ℝ) : Prop :=
  dP_dT_atV * (-dV_dP_atT) = dV_dT_atP

/-- Derived Cp-Cv identity in unnormalised response form. -/
theorem heatCapacityDifference_eq_unnormalized_response_form
    (D : EntropyResponseData) (dP_dT_atV : ℝ)
    (hMaxwell : D.dS_dV_atT = dP_dT_atV)
    (hResponse : EquationOfStateResponseRelation
      dP_dT_atV D.dV_dP_atT D.dV_dT_atP)
    (hden : -D.dV_dP_atT ≠ 0) :
    heatCapacityAtPressure D - heatCapacityAtVolume D =
      D.temperature * D.dV_dT_atP^2 / (-D.dV_dP_atT) := by
  rw [heatCapacityDifference_of_maxwell D dP_dT_atV hMaxwell]
  unfold EquationOfStateResponseRelation at hResponse
  apply (eq_div_iff hden).2
  calc
    D.temperature * dP_dT_atV * D.dV_dT_atP * (-D.dV_dP_atT) =
        D.temperature * D.dV_dT_atP * (dP_dT_atV * (-D.dV_dP_atT)) := by ring
    _ = D.temperature * D.dV_dT_atP * D.dV_dT_atP := by rw [hResponse]
    _ = D.temperature * D.dV_dT_atP ^ 2 := by ring

/-- Standard normalized form Cp-Cv = T V α² / κ_T. -/
theorem heatCapacityDifference_eq_TV_alpha_sq_div_kappa
    (D : EntropyResponseData) (dP_dT_atV : ℝ)
    (hV : D.volume ≠ 0)
    (hMaxwell : D.dS_dV_atT = dP_dT_atV)
    (hResponse : EquationOfStateResponseRelation
      dP_dT_atV D.dV_dP_atT D.dV_dT_atP)
    (hkappa : isothermalCompressibility D ≠ 0) :
    heatCapacityAtPressure D - heatCapacityAtVolume D =
      D.temperature * D.volume * (thermalExpansion D)^2 /
        isothermalCompressibility D := by
  have hden : -D.dV_dP_atT ≠ 0 := by
    intro hzero
    apply hkappa
    unfold isothermalCompressibility
    rw [hzero]
    simp
  have hdp : D.dV_dP_atT ≠ 0 := by
    intro hzero
    apply hden
    rw [hzero]
    simp
  rw [heatCapacityDifference_eq_unnormalized_response_form
    D dP_dT_atV hMaxwell hResponse hden]
  unfold thermalExpansion isothermalCompressibility
  field_simp [hV, hdp]

end ClassicalThermodynamics.Thermodynamics.ResponseFunctions
