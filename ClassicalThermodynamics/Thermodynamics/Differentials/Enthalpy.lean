import ClassicalThermodynamics.Thermodynamics.Differentials.Helmholtz
namespace ClassicalThermodynamics.Thermodynamics.Differentials

/-- Natural-variable differential data for H(S,P): dH = T dS + V dP. -/
structure EnthalpyDifferentialData where
  enthalpy : ℝ → ℝ → ℝ
  temperature : ℝ → ℝ → ℝ
  volume : ℝ → ℝ → ℝ
  entropyDerivative : ∀ S P,
    HasDerivAt (fun s => enthalpy s P) (temperature S P) S
  pressureDerivative : ∀ S P,
    HasDerivAt (fun p => enthalpy S p) (volume S P) P

end ClassicalThermodynamics.Thermodynamics.Differentials
