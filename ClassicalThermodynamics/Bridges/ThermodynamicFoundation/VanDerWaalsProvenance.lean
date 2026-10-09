import ClassicalThermodynamics.Thermodynamics.Derivatives.Provenance
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.DerivativeProvenance
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.ThirdDerivativeProvenance

namespace ClassicalThermodynamics.Bridges.ThermodynamicFoundation
open ClassicalThermodynamics.Thermodynamics.Derivatives
open ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
@[simp] theorem perturb_eq_coordinatePerturb
    (rho : State (ι := ι)) (i : ι) (t : ℝ) :
    perturb rho i t = coordinatePerturb rho i t := rfl

/-- The model-local family of chemical-potential certificates is exactly the
foundation's canonical coordinate-derivative certificate. -/
theorem chemicalPotentialDerived_iff_foundation
    (M : Model (ι := ι)) (rho : State (ι := ι)) :
    (∀ i, ChemicalPotentialDerived M rho i) ↔
      ClassicalThermodynamics.Thermodynamics.Derivatives.ChemicalPotentialDerived
        (freeEnergy M) (chemicalPotential M) rho := by
  rfl

/-- The model-local Hessian provenance predicate is definitionally the canonical
foundation predicate after identifying the shared coordinate perturbation. -/
theorem chemicalPotential_hasCoordinateDerivative_hessian_iff_foundation
    (M : Model (ι := ι)) (rho : State (ι := ι)) :
    HessianDerived M rho ↔
      ClassicalThermodynamics.Thermodynamics.Derivatives.HessianDerived
        (chemicalPotential M) (hessian M) rho := by
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The model directional state is the foundation directional perturbation. -/
@[simp] theorem directionalState_eq_directionalPerturb
    (rho q : State (ι := ι)) (t : ℝ) :
    directionalState rho q t = directionalPerturb rho q t := rfl

end ClassicalThermodynamics.Bridges.ThermodynamicFoundation
