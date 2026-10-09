import ClassicalThermodynamics.Thermodynamics.Equilibrium.ChemicalReaction
import ClassicalThermodynamics.Thermodynamics.Equilibrium.GibbsPhaseRule

/-!
# DeVoe (2020): chemical and phase equilibrium

Reaction-equilibrium wrappers preserve the local-minimum and reaction-path
derivative assumptions of the current formalization. The Gibbs phase-rule
wrapper is an algebraic variable/constraint count, not a proof of physical
existence or regularity.
-/

namespace ClassicalThermodynamics.Applications.DeVoe2020

open scoped BigOperators
open ClassicalThermodynamics.Thermodynamics.Equilibrium

variable {ι : Type*} [Fintype ι]

/-- DeVoe (2020), Eq. (11.7.1): `Delta_r G = sum_i nu_i mu_i`. -/
theorem eq_11_7_1_reaction_gibbs_energy
    (stoichiometry chemicalPotential : ι → ℝ) :
    reactionGibbsEnergy stoichiometry chemicalPotential =
      ∑ i, stoichiometry i * chemicalPotential i :=
  rfl

/-- DeVoe (2020), Eq. (11.7.2), the derivative of Gibbs energy along the
reaction-extent coordinate. This wrapper records the derivative premise; it
does not derive it from species-amount paths.
-/
theorem eq_11_7_2_reaction_extent_derivative
    (stoichiometry chemicalPotential : ι → ℝ)
    (gibbsEnergy : ℝ → ℝ) (extent : ℝ)
    (hDerivative :
      HasDerivAt gibbsEnergy
        (reactionGibbsEnergy stoichiometry chemicalPotential) extent) :
    HasDerivAt gibbsEnergy
      (reactionGibbsEnergy stoichiometry chemicalPotential) extent :=
  hDerivative

/-- DeVoe (2020), Eq. (11.7.4): an interior local Gibbs-energy minimum gives
`Delta_r G = 0`, given the reaction-extent derivative in Eq. (11.7.2).

DeVoe's derivation varies the reaction extent at fixed temperature and
pressure. The formal theorem makes the local-minimum and derivative
hypotheses explicit; it does not cover boundary optima.
-/
theorem eq_11_7_4_reaction_equilibrium
    (stoichiometry chemicalPotential : ι → ℝ)
    (gibbsEnergy : ℝ → ℝ) (extent : ℝ)
    (hMinimum : IsLocalMin gibbsEnergy extent)
    (hReactionDerivative :
      HasDerivAt gibbsEnergy
        (reactionGibbsEnergy stoichiometry chemicalPotential) extent) :
    ChemicalReactionEquilibrium stoichiometry chemicalPotential :=
  chemicalReactionEquilibrium_of_gibbsLocalMin
    stoichiometry chemicalPotential gibbsEnergy extent
    hMinimum hReactionDerivative

/-- DeVoe (2020), Eq. (13.1.1), the component form of the Gibbs phase rule.

The repository's count assumes independent equilibrium constraints and does
not prove that a particular component/phase combination is realizable.
-/
theorem eq_13_1_1_gibbs_phase_rule (components phases : ℕ) :
    phaseRuleDegreesOfFreedom components phases =
      (components : ℤ) - (phases : ℤ) + 2 :=
  gibbsPhaseRule components phases

end ClassicalThermodynamics.Applications.DeVoe2020
