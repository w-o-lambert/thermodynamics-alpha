import ClassicalThermodynamics.Thermodynamics.Differentials.CompositionMaxwell
namespace ClassicalThermodynamics.Thermodynamics.Derivatives

/-- Hessian symmetry as the thermodynamic content of composition mixed-partial commutation. -/
def HessianSymmetric {ι : Type*} (H : ι → ι → ℝ) : Prop :=
  ∀ i j, H i j = H j i

theorem hessianSymmetric_of_chemicalPotentialCrossDerivativesCommute
    {ι : Type*} {H : ι → ι → ℝ}
    (h : ClassicalThermodynamics.Thermodynamics.Differentials.ChemicalPotentialCrossDerivativesCommute H) :
    HessianSymmetric H := h

theorem chemicalPotentialCrossDerivativesCommute_of_hessianSymmetric
    {ι : Type*} {H : ι → ι → ℝ}
    (h : HessianSymmetric H) :
    ClassicalThermodynamics.Thermodynamics.Differentials.ChemicalPotentialCrossDerivativesCommute H := h

end ClassicalThermodynamics.Thermodynamics.Derivatives
