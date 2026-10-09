import Mathlib.Analysis.Calculus.Deriv.Basic
import ClassicalThermodynamics.Math.Functions.CoordinatePerturbation

/-!
# Partial molar volume and pressure dependence of chemical potential

For a mixture with amount vector `n`, the partial molar volume of component `i`
is the coordinate derivative

`Vbar_i = (∂V/∂n_i)_{T,P,n_j, j≠i}`.

At fixed temperature and composition, thermodynamics gives
`(∂ μ_i / ∂P) = Vbar_i`.  If `Vbar_i` is treated as pressure independent over
the pressure interval, integration gives
`μ_i(P₂)-μ_i(P₁)=Vbar_i(P₂-P₁)`.

For osmotic equilibrium across a solvent-permeable membrane, the solvent
chemical potentials are equal although the pressures differ by `Π`.  With the
solution-side pressure `P` and pure-solvent-side pressure `P+Π`, the mixing
contribution is therefore `μ_s = -Vbar_s Π`.  The sign depends on this explicit
pressure convention.
-/

namespace ClassicalThermodynamics.Thermodynamics

/-- Partial molar volume as the coordinate derivative of total volume with
respect to the amount of component `i`, evaluated at fixed `T`, `P`, and all
other component amounts. Those fixed external variables are parameters of the
supplied `totalVolume` function. -/
noncomputable def partialMolarVolume {ι : Type*} [DecidableEq ι]
    (totalVolume : (ι → ℝ) → ℝ) (n : ι → ℝ) (i : ι) : ℝ :=
  deriv (fun t => totalVolume (ClassicalThermodynamics.Math.Functions.coordinatePerturb n i t)) 0

/-- The differential pressure law `∂μ_i/∂P = Vbar_i`. -/
def ChemicalPotentialPressureLaw
    (mu : ℝ → ℝ) (vbar pressure : ℝ) : Prop :=
  HasDerivAt mu vbar pressure

/-- Chemical potential under the constant-partial-volume approximation. -/
noncomputable def chemicalPotentialAtPressure
    (muRef vbar pRef p : ℝ) : ℝ :=
  muRef + vbar * (p - pRef)

/-- Integrated constant-partial-volume pressure law. -/
theorem chemicalPotentialAtPressure_sub_reference
    (muRef vbar pRef p : ℝ) :
    chemicalPotentialAtPressure muRef vbar pRef p - muRef =
      vbar * (p - pRef) := by
  unfold chemicalPotentialAtPressure
  ring

/-- Solvent mixing chemical potential associated with osmotic pressure under the
convention `P_pure = P_solution + Π`. -/
noncomputable def solventChemicalPotentialFromOsmoticPressure
    (vbarSolvent osmoticPressure : ℝ) : ℝ :=
  -vbarSolvent * osmoticPressure

/-- The algebraic relation used as ACS Omega 2021a Equation (10). -/
@[simp] theorem solventChemicalPotentialFromOsmoticPressure_eq
    (vbarSolvent osmoticPressure : ℝ) :
    solventChemicalPotentialFromOsmoticPressure vbarSolvent osmoticPressure =
      -vbarSolvent * osmoticPressure := rfl

end ClassicalThermodynamics.Thermodynamics
