import ClassicalThermodynamics.Applications.Lekner1982.EquationComparison
namespace ClassicalThermodynamics.Applications.Lekner1982
open ClassicalThermodynamics.Methods.CoexistenceParametrisation
open ClassicalThermodynamics.Models.VanDerWaals.Pure
/-! Paper notation only. Derivations live in `EquationDerivation`; public wrappers in `Traceability`. -/
noncomputable def paperXLiquid (vLiquid b : ℝ) : ℝ := b / (vLiquid - b)
noncomputable def paperXGas (vGas b : ℝ) : ℝ := b / (vGas - b)
noncomputable def paperXLiquidParametric (y : ℝ) : ℝ := leknerF y * Real.exp y
noncomputable def paperXGasParametric (y : ℝ) : ℝ := leknerF y * Real.exp (-y)
noncomputable def paperReducedLiquidDensity (y : ℝ) : ℝ := 3 * leknerF y / (Real.exp (-y) + leknerF y)
noncomputable def paperReducedGasDensity (y : ℝ) : ℝ := 3 * leknerF y / (Real.exp y + leknerF y)
noncomputable def paperMeanReducedDensity (y : ℝ) : ℝ := 3 * leknerF y * (Real.cosh y + leknerF y) / leknerG y
noncomputable def paperReducedDensityDifference (y : ℝ) : ℝ := 6 * leknerF y * Real.sinh y / leknerG y
end ClassicalThermodynamics.Applications.Lekner1982
