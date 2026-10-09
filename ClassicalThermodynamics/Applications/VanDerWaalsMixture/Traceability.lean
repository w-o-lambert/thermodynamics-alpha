import ClassicalThermodynamics.Models.VanDerWaals.Mixture.PureSpecialisation
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Binary

/-!
## N-component van der Waals mixture

The mixture free energy is the model assumption. Component chemical potentials,
pressure, Hessian, coexistence, and the one-component reduction are consequences
or thin wrappers. The pair attraction matrix and component covolumes are explicit
model inputs; no combining rule is silently imposed.
-/

namespace ClassicalThermodynamics.Applications.VanDerWaalsMixture

open scoped BigOperators
open ClassicalThermodynamics.Models.VanDerWaals.Mixture

theorem verified_freeEnergy_modelAssumption
    {κ : Type*} [Fintype κ]
    (M : Model (ι := κ)) (rho : State (ι := κ)) :
    freeEnergy M rho =
      (∑ i, rho i * (Real.log (rho i) - 1)) -
      totalDensity rho * Real.log (freeVolumeFraction M rho) -
      ∑ i, ∑ j, alpha M i j / 2 * rho i * rho j := rfl

theorem verified_pressure_formula
    {κ : Type*} [Fintype κ]
    (M : Model (ι := κ)) (rho : State (ι := κ)) :
    pressure M rho =
      totalDensity rho / freeVolumeFraction M rho -
      ∑ i, ∑ j, alpha M i j / 2 * rho i * rho j := rfl

theorem verified_hessian_symmetry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Model (ι := ι)) (rho : State (ι := ι)) :
    (hessian M rho).IsSymm := hessian_isSymm M rho

theorem verified_oneComponent_pressure
    (M : ClassicalThermodynamics.Models.VanDerWaals.Pure.Model) (rho : ℝ) :
    pressure (ofPure M) (fun _ : Unit => rho) =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure M rho :=
  pressure_ofPure M rho

end ClassicalThermodynamics.Applications.VanDerWaalsMixture
