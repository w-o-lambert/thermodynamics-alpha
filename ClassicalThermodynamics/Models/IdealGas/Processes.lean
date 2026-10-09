import ClassicalThermodynamics.Models.IdealGas.Caloric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Models.IdealGas

/-- First-law balance with heat into the system and work done by the system
both taken as positive. -/
def FirstLawEnergyBalance (internalEnergyChange heatIntoSystem workBySystem : ℝ) : Prop :=
  internalEnergyChange = heatIntoSystem - workBySystem

/-- Quasistatic ideal-gas work along a reversible isothermal path, defined as
the pressure-volume integral with `P = n R T / V`. -/
noncomputable def reversibleIsothermalWork
    (M : Model) (n T V₁ V₂ : ℝ) : ℝ :=
  ∫ V in V₁..V₂, n * M.gasConstant * T / V

/-- Integrating the ideal-gas pressure along a reversible isotherm gives the
logarithmic work formula. -/
theorem reversibleIsothermalWork_eq
    (M : Model) (n T V₁ V₂ : ℝ)
    (_hAmount : 0 < n) (_hTemperature : 0 < T)
    (_hGasConstant : 0 < M.gasConstant)
    (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) :
    reversibleIsothermalWork M n T V₁ V₂ =
      n * M.gasConstant * T * Real.log (V₂ / V₁) := by
  let c := n * M.gasConstant * T
  unfold reversibleIsothermalWork
  change (∫ V in V₁..V₂, c / V) = n * M.gasConstant * T * Real.log (V₂ / V₁)
  have hPositive : ∀ V ∈ Set.uIcc V₁ V₂, 0 < V := by
    intro V hV
    rcases Set.mem_uIcc.mp hV with h | h
    · exact lt_of_lt_of_le hV₁ h.1
    · exact lt_of_lt_of_le hV₂ h.1
  have hderiv : ∀ V ∈ Set.uIcc V₁ V₂,
      HasDerivAt (fun x => c * Real.log x) (c / V) V := by
    intro V hV
    have hVpos := hPositive V hV
    convert (Real.hasDerivAt_log hVpos.ne').const_mul c using 1
    field_simp
  have hcontinuous : ContinuousOn (fun V : ℝ => c / V) (Set.uIcc V₁ V₂) := by
    apply continuousOn_const.div continuousOn_id
    intro V hV
    exact (ne_of_gt (hPositive V hV))
  have hint : IntervalIntegrable (fun V : ℝ => c / V)
      MeasureTheory.volume V₁ V₂ :=
    hcontinuous.intervalIntegrable
  calc
    (∫ V in V₁..V₂, c / V) =
        c * Real.log V₂ - c * Real.log V₁ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = n * M.gasConstant * T * Real.log (V₂ / V₁) := by
      rw [Real.log_div hV₂.ne' hV₁.ne']
      dsimp [c]
      ring

/-- Isothermal ideal-gas internal energy is unchanged under the
constant-heat-capacity model. -/
theorem internalEnergyChange_isothermal
    (M : Model) (C : ConstantHeatCapacity M) (n T₁ T₂ : ℝ)
    (hTemperature : T₂ = T₁) :
    internalEnergy M C n T₂ - internalEnergy M C n T₁ = 0 := by
  rw [internalEnergy_change, hTemperature]
  ring

/-- For an isothermal ideal-gas process, the first law gives `Q = W`. -/
theorem heat_eq_work_of_isothermal
    (M : Model) (C : ConstantHeatCapacity M) (n T₁ T₂ Q W : ℝ)
    (hBalance : FirstLawEnergyBalance
      (internalEnergy M C n T₂ - internalEnergy M C n T₁) Q W)
    (hTemperature : T₂ = T₁) :
    Q = W := by
  have hEnergy := internalEnergyChange_isothermal M C n T₁ T₂ hTemperature
  unfold FirstLawEnergyBalance at hBalance
  linarith

/-- For an adiabatic process, the first law identifies work done by the
system with minus its internal-energy change. -/
theorem work_eq_neg_internalEnergyChange_of_adiabatic
    (internalEnergyChange heatIntoSystem workBySystem : ℝ)
    (hBalance : FirstLawEnergyBalance
      internalEnergyChange heatIntoSystem workBySystem)
    (hAdiabatic : heatIntoSystem = 0) :
    workBySystem = -internalEnergyChange := by
  unfold FirstLawEnergyBalance at hBalance
  linarith

theorem entropyChange_isothermal
    (M : Model) (C : ConstantHeatCapacity M) (n T₁ T₂ V₁ V₂ : ℝ)
    (hTemperature : T₂ = T₁) (_hT₁ : 0 < T₁)
    (_hV₁ : 0 < V₁) (_hV₂ : 0 < V₂) :
    entropyChange M C n T₁ T₂ V₁ V₂ =
      n * M.gasConstant * Real.log (V₂ / V₁) := by
  unfold entropyChange
  rw [hTemperature]
  simp

theorem entropyChange_isochoric
    (M : Model) (C : ConstantHeatCapacity M) (n T₁ T₂ V₁ V₂ : ℝ)
    (hVolume : V₂ = V₁) (_hT₁ : 0 < T₁) (_hT₂ : 0 < T₂)
    (_hV₁ : 0 < V₁) :
    entropyChange M C n T₁ T₂ V₁ V₂ =
      n * C.heatCapacityAtVolume * Real.log (T₂ / T₁) := by
  unfold entropyChange
  rw [hVolume]
  simp

/-- Equal-pressure ideal-gas states have matching temperature and volume
ratios. Nonzero pressure, amount, gas constant, and initial temperature are
required for the ratio form. -/
theorem volumeRatio_eq_temperatureRatio_of_equalPressure
    (M : Model) (n T₁ T₂ V₁ V₂ P : ℝ)
    (hEOS₁ : EquationOfState M n T₁ V₁ P)
    (hEOS₂ : EquationOfState M n T₂ V₂ P)
    (hPressure : P ≠ 0) (hAmount : n ≠ 0)
    (hGasConstant : M.gasConstant ≠ 0) (hT₁ : T₁ ≠ 0) :
    V₂ / V₁ = T₂ / T₁ := by
  have hV₁ : V₁ = n * M.gasConstant * T₁ / P := by
    apply (eq_div_iff hPressure).2
    change P * V₁ = n * M.gasConstant * T₁ at hEOS₁
    nlinarith [hEOS₁]
  have hV₂ : V₂ = n * M.gasConstant * T₂ / P := by
    apply (eq_div_iff hPressure).2
    change P * V₂ = n * M.gasConstant * T₂ at hEOS₂
    nlinarith [hEOS₂]
  rw [hV₁, hV₂]
  have hNR : n * M.gasConstant ≠ 0 := mul_ne_zero hAmount hGasConstant
  field_simp [hPressure, hNR, hT₁]

/-- At constant pressure, the ideal-gas entropy change is `n Cp log(T₂/T₁)`. -/
theorem entropyChange_isobaric
    (M : Model) (C : ConstantHeatCapacity M) (n T₁ T₂ V₁ V₂ P : ℝ)
    (hEOS₁ : EquationOfState M n T₁ V₁ P)
    (hEOS₂ : EquationOfState M n T₂ V₂ P)
    (hPressure : 0 < P) (hAmount : 0 < n)
    (hT₁ : 0 < T₁) (_hT₂ : 0 < T₂)
    (_hV₁ : 0 < V₁) (_hV₂ : 0 < V₂) :
    entropyChange M C n T₁ T₂ V₁ V₂ =
      n * heatCapacityAtPressure M C * Real.log (T₂ / T₁) := by
  have hRatio := volumeRatio_eq_temperatureRatio_of_equalPressure M n T₁ T₂
    V₁ V₂ P hEOS₁ hEOS₂ (ne_of_gt hPressure) (ne_of_gt hAmount)
    (ne_of_gt C.gasConstant_pos) (ne_of_gt hT₁)
  unfold entropyChange
  rw [hRatio]
  unfold heatCapacityAtPressure
  ring

/-- An isentropic ideal-gas change with nonzero amount satisfies the logarithmic
form of the reversible-adiabatic relation. -/
theorem isentropic_log_relation
    (M : Model) (C : ConstantHeatCapacity M) (n T₁ T₂ V₁ V₂ : ℝ)
    (hAmount : 0 < n) (_hT₁ : 0 < T₁) (_hT₂ : 0 < T₂)
    (_hV₁ : 0 < V₁) (_hV₂ : 0 < V₂)
    (hIsentropic : entropyChange M C n T₁ T₂ V₁ V₂ = 0) :
    C.heatCapacityAtVolume * Real.log (T₂ / T₁) +
      M.gasConstant * Real.log (V₂ / V₁) = 0 := by
  have hFactored :
      n * (C.heatCapacityAtVolume * Real.log (T₂ / T₁) +
        M.gasConstant * Real.log (V₂ / V₁)) = 0 := by
    rw [← hIsentropic]
    unfold entropyChange
    ring
  exact (mul_eq_zero.mp hFactored).resolve_left (ne_of_gt hAmount)

end ClassicalThermodynamics.Models.IdealGas
