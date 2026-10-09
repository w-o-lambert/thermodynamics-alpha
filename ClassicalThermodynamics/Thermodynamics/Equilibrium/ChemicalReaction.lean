import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Thermodynamics.Equilibrium

open scoped BigOperators

/-- Gibbs-energy change per unit reaction extent, `ΔᵣG = ∑ᵢ νᵢ μᵢ`. -/
def reactionGibbsEnergy {ι : Type*} [Fintype ι]
    (stoichiometry chemicalPotential : ι → ℝ) : ℝ :=
  ∑ i, stoichiometry i * chemicalPotential i

/-- Interior chemical reaction equilibrium: the Gibbs-energy derivative with
respect to reaction extent vanishes. -/
def ChemicalReactionEquilibrium {ι : Type*} [Fintype ι]
    (stoichiometry chemicalPotential : ι → ℝ) : Prop :=
  reactionGibbsEnergy stoichiometry chemicalPotential = 0

/-- For an interior feasible reaction extent, a local Gibbs-energy minimum
implies `∑ᵢ νᵢ μᵢ = 0`, assuming the reaction-path derivative is the usual
stoichiometric sum. Boundary equilibria may instead satisfy one-sided
optimality conditions. -/
theorem chemicalReactionEquilibrium_of_gibbsLocalMin
    {ι : Type*} [Fintype ι] (stoichiometry chemicalPotential : ι → ℝ)
    (gibbsEnergy : ℝ → ℝ) (extent : ℝ)
    (hMinimum : IsLocalMin gibbsEnergy extent)
    (hReactionDerivative :
      HasDerivAt gibbsEnergy
        (reactionGibbsEnergy stoichiometry chemicalPotential) extent) :
    ChemicalReactionEquilibrium stoichiometry chemicalPotential := by
  unfold ChemicalReactionEquilibrium
  exact hMinimum.hasDerivAt_eq_zero hReactionDerivative

/-- Chemical potentials for an ideal activity-based species:
`μᵢ = μᵢ° + RT log(aᵢ)`. -/
noncomputable def idealActivityChemicalPotential
    (standardPotential gasConstant temperature activity : ℝ) : ℝ :=
  standardPotential + gasConstant * temperature * Real.log activity

/-- Logarithm of the reaction quotient, `log Q = ∑ᵢ νᵢ log(aᵢ)`. -/
noncomputable def reactionLogQuotient {ι : Type*} [Fintype ι]
    (stoichiometry activity : ι → ℝ) : ℝ :=
  ∑ i, stoichiometry i * Real.log (activity i)

/-- The reaction quotient represented as the exponential of its logarithm,
allowing real-valued stoichiometric coefficients. -/
noncomputable def reactionQuotient {ι : Type*} [Fintype ι]
    (stoichiometry activity : ι → ℝ) : ℝ :=
  Real.exp (reactionLogQuotient stoichiometry activity)

/-- Standard reaction Gibbs energy. -/
def standardReactionGibbsEnergy {ι : Type*} [Fintype ι]
    (stoichiometry standardPotential : ι → ℝ) : ℝ :=
  reactionGibbsEnergy stoichiometry standardPotential

/-- The equilibrium constant corresponding to the standard reaction Gibbs
energy, `K = exp(-ΔᵣG°/(RT))`. -/
noncomputable def reactionEquilibriumConstant {ι : Type*} [Fintype ι]
    (stoichiometry standardPotential : ι → ℝ)
    (gasConstant temperature : ℝ) : ℝ :=
  Real.exp
    (-standardReactionGibbsEnergy stoichiometry standardPotential /
      (gasConstant * temperature))

/-- Substituting ideal activity-based chemical potentials into `ΔᵣG`
gives `ΔᵣG = ΔᵣG° + RT log Q`. -/
lemma reactionGibbsEnergy_idealActivity
    {ι : Type*} [Fintype ι]
    (stoichiometry standardPotential activity : ι → ℝ)
    (gasConstant temperature : ℝ) :
    reactionGibbsEnergy stoichiometry
        (fun i => idealActivityChemicalPotential
          (standardPotential i) gasConstant temperature (activity i)) =
      standardReactionGibbsEnergy stoichiometry standardPotential +
        gasConstant * temperature *
          reactionLogQuotient stoichiometry activity := by
  simp only [reactionGibbsEnergy, standardReactionGibbsEnergy,
    idealActivityChemicalPotential, reactionLogQuotient]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  apply congrArg (fun s : ℝ =>
    (∑ i, stoichiometry i * standardPotential i) + s)
  calc
    (∑ i, stoichiometry i *
        (gasConstant * temperature * Real.log (activity i))) =
      ∑ i, (gasConstant * temperature) *
        (stoichiometry i * Real.log (activity i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = gasConstant * temperature *
        (∑ i, stoichiometry i * Real.log (activity i)) := by
          rw [← Finset.mul_sum]

/-- At reaction equilibrium, ideal activities obey the logarithmic
mass-action relation `log Q = -ΔᵣG°/(RT)`. -/
theorem logReactionQuotient_eq_neg_standardGibbs_div_RT
    {ι : Type*} [Fintype ι]
    (stoichiometry standardPotential activity : ι → ℝ)
    (gasConstant temperature : ℝ)
    (_hActivities : ∀ i, 0 < activity i)
    (hGasConstant : 0 < gasConstant) (hTemperature : 0 < temperature)
    (hEquilibrium : ChemicalReactionEquilibrium stoichiometry
      (fun i => idealActivityChemicalPotential
        (standardPotential i) gasConstant temperature (activity i))) :
    reactionLogQuotient stoichiometry activity =
      -standardReactionGibbsEnergy stoichiometry standardPotential /
        (gasConstant * temperature) := by
  have hFormula := reactionGibbsEnergy_idealActivity
    stoichiometry standardPotential activity gasConstant temperature
  unfold ChemicalReactionEquilibrium at hEquilibrium
  rw [hEquilibrium] at hFormula
  have hRT : gasConstant * temperature ≠ 0 :=
    mul_ne_zero (ne_of_gt hGasConstant) (ne_of_gt hTemperature)
  apply (eq_div_iff hRT).2
  nlinarith [hFormula]

/-- Exponentiating the mass-action relation identifies the reaction quotient
with its equilibrium constant. -/
theorem reactionQuotient_eq_equilibriumConstant_of_equilibrium
    {ι : Type*} [Fintype ι]
    (stoichiometry standardPotential activity : ι → ℝ)
    (gasConstant temperature : ℝ)
    (hActivities : ∀ i, 0 < activity i)
    (hGasConstant : 0 < gasConstant) (hTemperature : 0 < temperature)
    (hEquilibrium : ChemicalReactionEquilibrium stoichiometry
      (fun i => idealActivityChemicalPotential
        (standardPotential i) gasConstant temperature (activity i))) :
    reactionQuotient stoichiometry activity =
      reactionEquilibriumConstant stoichiometry standardPotential
        gasConstant temperature := by
  unfold reactionQuotient reactionEquilibriumConstant
  rw [logReactionQuotient_eq_neg_standardGibbs_div_RT
    stoichiometry standardPotential activity gasConstant temperature
    hActivities hGasConstant hTemperature hEquilibrium]

end ClassicalThermodynamics.Thermodynamics.Equilibrium
