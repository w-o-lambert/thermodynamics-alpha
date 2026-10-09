import ClassicalThermodynamics.Models.RegularMixture.BinarySymmetric

/-!
# Kirkwood–Oppenheim: symmetric binary regular solutions

Equation wrappers delegate to the regular-mixture model layer, which contains
the definitions and proofs.
-/

namespace ClassicalThermodynamics.Applications.KirkwoodOppenheim1961

open ClassicalThermodynamics.Models.RegularMixture

/-- Kirkwood–Oppenheim, Chapter 11, Eq. (11-127): component 1 excess chemical
potential in the symmetric binary regular-solution model. -/
theorem eq_11_127_excessChemicalPotential1
    (B x2 : ℝ) :
    excessChemicalPotential1 B x2 = B * x2 ^ 2 :=
  rfl

/-- Kirkwood–Oppenheim, Chapter 11, Eq. (11-128): component 2 excess chemical
potential in the symmetric binary regular-solution model. -/
theorem eq_11_128_excessChemicalPotential2
    (B x1 : ℝ) :
    excessChemicalPotential2 B x1 = B * x1 ^ 2 :=
  rfl

/-- Kirkwood–Oppenheim, Chapter 11, Eq. (11-129): the weighted excess
chemical potentials give the integral heat of mixing. -/
theorem eq_11_129_weightedExcessChemicalPotentials
    (B x1 x2 : ℝ) (hsum : x1 + x2 = 1) :
    x1 * excessChemicalPotential1 B x2 +
      x2 * excessChemicalPotential2 B x1 =
        integralHeatOfMixing B x1 x2 :=
  weighted_excessChemicalPotentials_eq_integralHeat B x1 x2 hsum

/-- Kirkwood–Oppenheim, Chapter 11, Eq. (11-130): the interaction coefficient
is four times the equimolar integral heat of mixing. -/
theorem eq_11_130_interactionCoefficient
    (B : ℝ) :
    B = 4 * integralHeatOfMixing B (1 / 2) (1 / 2) :=
  interaction_eq_four_mul_equimolarHeat B

/-- Regular-solution Gibbs mixing energy separates into ideal entropy and the
integral heat contribution. -/
theorem regularSolution_gibbsMixing_decomposition
    (R T B x1 x2 : ℝ) :
    gibbsOfMixing R T B x1 x2 =
      -T * entropyOfMixing R x1 x2 +
        integralHeatOfMixing B x1 x2 :=
  gibbsOfMixing_eq_entropy_and_integralHeat R T B x1 x2

end ClassicalThermodynamics.Applications.KirkwoodOppenheim1961
