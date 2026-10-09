import ClassicalThermodynamics.Thermodynamics.Differentials.Enthalpy
namespace ClassicalThermodynamics.Thermodynamics.Differentials

/-- Natural-variable differential data for G(T,P): dG = -S dT + V dP. -/
structure GibbsDifferentialData where
  gibbs : ℝ → ℝ → ℝ
  entropy : ℝ → ℝ → ℝ
  volume : ℝ → ℝ → ℝ
  temperatureDerivative : ∀ T P,
    HasDerivAt (fun t => gibbs t P) (-entropy T P) T
  pressureDerivative : ∀ T P,
    HasDerivAt (fun p => gibbs T p) (volume T P) P

end ClassicalThermodynamics.Thermodynamics.Differentials
