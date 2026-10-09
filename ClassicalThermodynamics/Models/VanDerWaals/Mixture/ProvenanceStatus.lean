import ClassicalThermodynamics.Models.VanDerWaals.Mixture.DerivativeProvenance
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.ThirdDerivativeProvenance

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bundled analytic provenance required for a fully calculus-derived model. -/
structure FullDerivativeProvenance (M : Model (ι := ι))
    (rho : State (ι := ι)) : Prop where
  chemicalPotential : ∀ i, ChemicalPotentialDerived M rho i
  hessian : HessianDerived M rho
  thirdDirectional : ∀ q, ThirdDirectionalDerivativeDerived M rho q

/-- Existing derivative certificates bundle into the full provenance object. -/
theorem fullDerivativeProvenance_of_certificates
    (M : Model (ι := ι)) (rho : State (ι := ι))
    (hmu : ∀ i, ChemicalPotentialDerived M rho i)
    (hH : HessianDerived M rho)
    (h3 : ∀ q, ThirdDirectionalDerivativeDerived M rho q) :
    FullDerivativeProvenance M rho := ⟨hmu, hH, h3⟩

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
