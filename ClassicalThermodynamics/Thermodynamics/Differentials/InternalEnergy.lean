import ClassicalThermodynamics.Thermodynamics.Derivatives.Provenance
namespace ClassicalThermodynamics.Thermodynamics.Differentials

/-- Natural-variable differential data for U(S,V): dU = T dS - P dV. -/
structure InternalEnergyDifferentialData where
  internalEnergy : ℝ → ℝ → ℝ
  temperature : ℝ → ℝ → ℝ
  pressure : ℝ → ℝ → ℝ
  entropyDerivative : ∀ S V,
    HasDerivAt (fun s => internalEnergy s V) (temperature S V) S
  volumeDerivative : ∀ S V,
    HasDerivAt (fun v => internalEnergy S v) (-pressure S V) V

end ClassicalThermodynamics.Thermodynamics.Differentials
