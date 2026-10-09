import ClassicalThermodynamics.Models.IdealGas.Model
import ClassicalThermodynamics.Models.IdealGas.Processes
import ClassicalThermodynamics.Models.IdealGas.Caloric
import ClassicalThermodynamics.Models.IdealMixture.Raoult
import ClassicalThermodynamics.Models.RegularMixture.Model
import ClassicalThermodynamics.Models.DiluteSolution.FreezingPointDepression
import ClassicalThermodynamics.Models.DiluteSolution.OsmoticPressure

/-!
# DeVoe (2020): selected model equations

These wrappers are restricted to equations that match the current model
definitions. Source assumptions are called out where the formal definitions
omit them.
-/

namespace ClassicalThermodynamics.Applications.DeVoe2020

open ClassicalThermodynamics.Models.IdealGas
open ClassicalThermodynamics.Models.IdealMixture
open ClassicalThermodynamics.Models.RegularMixture
open ClassicalThermodynamics.Models.DiluteSolution

/-- DeVoe (2020), Eq. (2.2.9) with ideal-gas compressibility factor `Z = 1`.
The source equation defines `Z = p V_m/(R T)`; this equivalent statement is
expressed using the repository's total amount `n`.
-/
theorem eq_2_2_9_ideal_gas_equation
    (M : ClassicalThermodynamics.Models.IdealGas.Model) (n T V P : ℝ)
    (hCompressibility :
      P * V / (n * M.gasConstant * T) = 1) :
    ClassicalThermodynamics.Models.IdealGas.EquationOfState M n T V P := by
  change P * V = n * M.gasConstant * T
  have hDenominator : n * M.gasConstant * T ≠ 0 := by
    intro hZero
    rw [hZero] at hCompressibility
    norm_num at hCompressibility
  have hProduct :
      P * V = n * M.gasConstant * T := by
    simpa using (div_eq_iff hDenominator).mp hCompressibility
  exact hProduct

/-- DeVoe (2020), Eq. (3.5.1), reversible isothermal ideal-gas work.

The formal theorem retains positive amount, temperature, gas constant, and
endpoint volumes; the path is the reversible isothermal ideal-gas path.
-/
theorem eq_3_5_1_reversible_isothermal_work
    (M : ClassicalThermodynamics.Models.IdealGas.Model) (n T V₁ V₂ : ℝ)
    (hAmount : 0 < n) (hTemperature : 0 < T)
    (hGasConstant : 0 < M.gasConstant)
    (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) :
    reversibleIsothermalWork M n T V₁ V₂ =
      n * M.gasConstant * T * Real.log (V₂ / V₁) :=
  reversibleIsothermalWork_eq M n T V₁ V₂
    hAmount hTemperature hGasConstant hV₁ hV₂

/-- Integrated constant-heat-capacity form of DeVoe (2020), Eq. (3.5.3),
`dU = C_V dT` for a closed ideal gas.

The repository's model assumes constant `C_V`, so this finite-change formula
is more specific than DeVoe's differential relation.
-/
theorem eq_3_5_3_internal_energy_change
    (M : ClassicalThermodynamics.Models.IdealGas.Model)
    (C : ConstantHeatCapacity M) (n T₁ T₂ : ℝ) :
    internalEnergy M C n T₂ - internalEnergy M C n T₁ =
      n * C.heatCapacityAtVolume * (T₂ - T₁) :=
  internalEnergy_change M C n T₁ T₂

/-- Isothermal internal-energy invariance obtained from DeVoe's Eq. (3.5.3)
under the repository's constant-heat-capacity model. -/
theorem isothermal_internal_energy_change_from_eq_3_5_3
    (M : ClassicalThermodynamics.Models.IdealGas.Model)
    (C : ConstantHeatCapacity M) (n T₁ T₂ : ℝ)
    (hTemperature : T₂ = T₁) :
    internalEnergy M C n T₂ - internalEnergy M C n T₁ = 0 := by
  rw [eq_3_5_3_internal_energy_change, hTemperature]
  ring

/-- Isothermal `Q = W`, derived from Eq. (3.5.3) and the process first-law
balance with heat into the system and work by the system positive. -/
theorem isothermal_heat_eq_work_from_first_law
    (M : ClassicalThermodynamics.Models.IdealGas.Model)
    (C : ConstantHeatCapacity M) (n T₁ T₂ Q W : ℝ)
    (hBalance : FirstLawEnergyBalance
      (internalEnergy M C n T₂ - internalEnergy M C n T₁) Q W)
    (hTemperature : T₂ = T₁) :
    Q = W :=
  heat_eq_work_of_isothermal M C n T₁ T₂ Q W hBalance hTemperature

/-- Adiabatic work consequence of the first-law process balance, with heat
into the system and work by the system positive. -/
theorem adiabatic_work_from_first_law
    (internalEnergyChange heatIntoSystem workBySystem : ℝ)
    (hBalance : FirstLawEnergyBalance
      internalEnergyChange heatIntoSystem workBySystem)
    (hAdiabatic : heatIntoSystem = 0) :
    workBySystem = -internalEnergyChange :=
  work_eq_neg_internalEnergyChange_of_adiabatic
    internalEnergyChange heatIntoSystem workBySystem hBalance hAdiabatic

/-- DeVoe (2020), Eq. (9.4.2), Raoult's law for partial pressure. -/
theorem eq_9_4_2_raoult_partial_pressure
    (x_i saturationPressure : ℝ) :
    raoultPartialPressure x_i saturationPressure =
      x_i * saturationPressure :=
  rfl

/-- DeVoe (2020), Eq. (11.1.34), binary regular-solution excess molar Gibbs
energy. The `interaction` parameter represents DeVoe's
`Delta U_mix / n` coefficient; the source assumes zero excess molar volume and
zero excess molar entropy.
-/
theorem eq_11_1_34_regular_solution_excess_gibbs
    (interaction x : ℝ) :
    excessGibbs interaction x = interaction * x * (1 - x) :=
  rfl

/-- DeVoe (2020), Eq. (12.4.12), dilute binary-solution freezing-point
depression for a nonelectrolyte (`nu = 1`). -/
theorem eq_12_4_12_freezing_point_depression
    (cryoscopicConstant molality : ℝ) :
    freezingPointDepression cryoscopicConstant molality =
      cryoscopicConstant * molality :=
  rfl

/-- DeVoe (2020), Eq. (12.4.25), van 't Hoff osmotic pressure for a dilute
binary solution of a nonelectrolyte (`nu = 1`). -/
theorem eq_12_4_25_dilute_osmotic_pressure
    (R T concentration : ℝ) :
    idealDiluteOsmoticPressure R T concentration =
      R * T * concentration :=
  rfl

end ClassicalThermodynamics.Applications.DeVoe2020
