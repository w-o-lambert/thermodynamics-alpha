import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring.RingNF
import ClassicalThermodynamics.Models.RegularMixture.Model

namespace ClassicalThermodynamics.Models.RegularMixture

/-- Component 1 excess chemical potential in the symmetric binary regular
solution model. `x2` is the mole fraction of component 2. -/
def excessChemicalPotential1 (interaction x2 : ℝ) : ℝ :=
  interaction * x2 ^ 2

/-- Component 2 excess chemical potential in the symmetric binary regular
solution model. `x1` is the mole fraction of component 1. -/
def excessChemicalPotential2 (interaction x1 : ℝ) : ℝ :=
  interaction * x1 ^ 2

/-- Integral heat of mixing in the symmetric binary regular solution model. -/
def integralHeatOfMixing (interaction x1 x2 : ℝ) : ℝ :=
  interaction * x1 * x2

/-- The mole-fraction weighted excess chemical potentials give the integral
heat of mixing on the binary composition simplex. -/
theorem weighted_excessChemicalPotentials_eq_integralHeat
    (interaction x1 x2 : ℝ) (hsum : x1 + x2 = 1) :
    x1 * excessChemicalPotential1 interaction x2 +
      x2 * excessChemicalPotential2 interaction x1 =
        integralHeatOfMixing interaction x1 x2 := by
  unfold excessChemicalPotential1 excessChemicalPotential2 integralHeatOfMixing
  calc
    x1 * (interaction * x2 ^ 2) +
        x2 * (interaction * x1 ^ 2) =
      interaction * x1 * x2 * (x1 + x2) := by ring
    _ = interaction * x1 * x2 := by rw [hsum]; ring

/-- At equimolar composition, four times the integral heat of mixing equals
the interaction coefficient. -/
theorem interaction_eq_four_mul_equimolarHeat (interaction : ℝ) :
    interaction =
      4 * integralHeatOfMixing interaction (1 / 2) (1 / 2) := by
  unfold integralHeatOfMixing
  ring

/-- Ideal configurational entropy retained by a binary regular solution. -/
noncomputable def entropyOfMixing (gasConstant x1 x2 : ℝ) : ℝ :=
  -gasConstant *
    (x1 * Real.log x1 + x2 * Real.log x2)

/-- Binary regular-solution Gibbs energy of mixing: ideal entropy plus
excess enthalpy. -/
noncomputable def gibbsOfMixing
    (gasConstant temperature interaction x1 x2 : ℝ) : ℝ :=
  gasConstant * temperature *
      (x1 * Real.log x1 + x2 * Real.log x2) +
    integralHeatOfMixing interaction x1 x2

/-- The Gibbs energy of mixing separates into the ideal entropy contribution
and the regular-solution integral heat. -/
theorem gibbsOfMixing_eq_entropy_and_integralHeat
    (gasConstant temperature interaction x1 x2 : ℝ) :
    gibbsOfMixing gasConstant temperature interaction x1 x2 =
      -temperature * entropyOfMixing gasConstant x1 x2 +
        integralHeatOfMixing interaction x1 x2 := by
  unfold gibbsOfMixing entropyOfMixing
  ring

end ClassicalThermodynamics.Models.RegularMixture
