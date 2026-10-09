import ClassicalThermodynamics.Thermodynamics.Differentials.InternalEnergy
namespace ClassicalThermodynamics.Thermodynamics.Differentials

/-- Natural-variable differential data for F(T,V): dF = -S dT - P dV. -/
structure HelmholtzDifferentialData where
  helmholtz : ℝ → ℝ → ℝ
  entropy : ℝ → ℝ → ℝ
  pressure : ℝ → ℝ → ℝ
  temperatureDerivative : ∀ T V,
    HasDerivAt (fun t => helmholtz t V) (-entropy T V) T
  volumeDerivative : ∀ T V,
    HasDerivAt (fun v => helmholtz T v) (-pressure T V) V

end ClassicalThermodynamics.Thermodynamics.Differentials
