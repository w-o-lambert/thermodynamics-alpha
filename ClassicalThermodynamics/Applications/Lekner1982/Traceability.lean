import ClassicalThermodynamics.Applications.Lekner1982.EquationDerivation
import ClassicalThermodynamics.Applications.Lekner1982.Parametrisation

/-!
# Lekner, American Journal of Physics 50 (1982), 161-163
-/

namespace ClassicalThermodynamics.Applications.Lekner1982

open ClassicalThermodynamics.Methods.CoexistenceParametrisation
open ClassicalThermodynamics.Models.VanDerWaals.Pure

/-- Eq. (1): the reduced van der Waals equation of state. -/
noncomputable def equation1Pressure (T n : ℝ) : ℝ := 8 * T * n / (3 - n) - 3 * n^2

@[simp] theorem verified_equation1 (T n : ℝ) :
    equation1Pressure T n = 8 * T * n / (3 - n) - 3 * n^2 := rfl

/-- Eq. (2): equal coexistence pressure on both branches. -/
def Equation2 (T p nl ng : ℝ) : Prop :=
  equation1Pressure T nl = p ∧ equation1Pressure T ng = p

@[simp] theorem verified_equation2 (T p nl ng : ℝ) :
    Equation2 T p nl ng ↔ equation1Pressure T nl = p ∧ equation1Pressure T ng = p := Iff.rfl

/-- Eq. (5): the parameter-free coexistence relation in free-volume variables. -/
def Equation5 (xl xg : ℝ) : Prop :=
  Real.log (xl / xg) / (xl - xg) = (2 + xl + xg) / (xl + xg + 2 * xl * xg)

@[simp] theorem verified_equation5 (xl xg : ℝ) :
    Equation5 xl xg ↔
      Real.log (xl / xg) / (xl - xg) = (2 + xl + xg) / (xl + xg + 2 * xl * xg) := Iff.rfl

/-! Thin paper-facing wrappers; substantive proofs are in `EquationDerivation`. -/

/-- Eq. (10), liquid branch. -/
theorem verified_equation10_liquid
    {y : ℝ} (h : Real.sinh y * Real.cosh y - y ≠ 0) :
    vdwLiquidFreeVolume (repositoryParameter y) = paperXLiquidParametric y :=
  derive_equation10_liquid h

/-- Eq. (10), gas branch. -/
theorem verified_equation10_gas
    {y : ℝ} (h : Real.sinh y * Real.cosh y - y ≠ 0) :
    vdwGasFreeVolume (repositoryParameter y) = paperXGasParametric y :=
  derive_equation10_gas h

/-- Eq. (11), the logarithmic branch-ratio relation. -/
theorem verified_equation11
    {y : ℝ} (h : leknerF y ≠ 0) :
    Real.log (paperXLiquidParametric y / paperXGasParametric y) = 2 * y :=
  derive_equation11 h

/-- Eq. (12), the auxiliary function `f(y)`. -/
theorem verified_equation12 (y : ℝ) :
    leknerF y =
      (y * Real.cosh y - Real.sinh y) /
        (Real.sinh y * Real.cosh y - y) :=
  rfl

/-- The reduced liquid density in the paper's parametrisation. -/
theorem verified_reducedLiquidDensity
    {y : ℝ} (h : Real.sinh y * Real.cosh y - y ≠ 0)
    (hl : Real.exp (-y) + leknerF y ≠ 0) :
    reducedLiquidDensityLekner y = paperReducedLiquidDensity y :=
  derive_reducedLiquidDensity h hl

/-- The reduced gas density in the paper's parametrisation. -/
theorem verified_reducedGasDensity
    {y : ℝ} (h : Real.sinh y * Real.cosh y - y ≠ 0)
    (hg : Real.exp y + leknerF y ≠ 0) :
    reducedGasDensityLekner y = paperReducedGasDensity y :=
  derive_reducedGasDensity h hg

/-- Eq. (13), the reduced coexistence temperature. -/
theorem verified_equation13
    {y : ℝ} (h : Real.sinh y * Real.cosh y - y ≠ 0) :
    reducedTemperature y =
      27 * leknerF y * (Real.cosh y + leknerF y) /
        (4 * (leknerG y)^2) :=
  derive_equation13 h

/-- Eq. (14), the reduced coexistence pressure. -/
theorem verified_equation14
    {y : ℝ} (h : Real.sinh y * Real.cosh y - y ≠ 0) :
    reducedPressure y =
      27 * (leknerF y)^2 * (1 - (leknerF y)^2) / (leknerG y)^2 :=
  derive_equation14 h

/-- Eq. (15), the mean reduced density. -/
theorem verified_equation15
    {y : ℝ} (h : Real.sinh y * Real.cosh y - y ≠ 0)
    (hl : Real.exp (-y) + leknerF y ≠ 0)
    (hg : Real.exp y + leknerF y ≠ 0) (hg' : leknerG y ≠ 0) :
    (paperReducedLiquidDensity y + paperReducedGasDensity y) / 2 =
      paperMeanReducedDensity y :=
  derive_equation15 h hl hg hg'

/-- Eq. (16), the reduced density difference. -/
theorem verified_equation16
    {y : ℝ} (h : Real.sinh y * Real.cosh y - y ≠ 0)
    (hl : Real.exp (-y) + leknerF y ≠ 0)
    (hg : Real.exp y + leknerF y ≠ 0) (hg' : leknerG y ≠ 0) :
    paperReducedLiquidDensity y - paperReducedGasDensity y =
      paperReducedDensityDifference y :=
  derive_equation16 h hl hg hg'

/-- Identification of the repository midpoint with Lekner's `f(y)`. -/
theorem verified_lekner_f_mapping
    {y : ℝ} (h : Real.sinh y * Real.cosh y - y ≠ 0) :
    vdwGeometricMidpoint (2 * y) = leknerF y := by
  simpa [repositoryParameter] using midpoint_eq_leknerF h

end ClassicalThermodynamics.Applications.Lekner1982
