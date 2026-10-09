import ClassicalThermodynamics.Models.Berthelot.Mixture.Thermodynamics
import ClassicalThermodynamics.Models.Berthelot.Pure.Model
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.FixedCompositionCoexistence

open scoped BigOperators

namespace ClassicalThermodynamics.Models.Berthelot.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Mole fractions for fixed-composition mixture calculations. -/
def NormalizedComposition (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-- Linear covolume mixing rule used by the multicomponent van der Waals model. -/
noncomputable def mixtureCovolume (M : Model (ι := ι)) (x : ι → ℝ) : ℝ :=
  ∑ i, x i * M.excludedVolume i

/-- Quadratic pair-attraction mixing rule used by the multicomponent van der
Waals model. -/
noncomputable def mixtureAttraction (M : Model (ι := ι)) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M.attraction i j * x j / 2

/-- Dimensional Berthelot pressure along a fixed-composition ray. -/
noncomputable def pressureTVAtComposition
    (M : Model (ι := ι)) (x : ι → ℝ)
    (temperature molarVolume : ℝ) : ℝ :=
  M.gasConstant * temperature /
      (molarVolume - mixtureCovolume M x) -
    mixtureAttraction M x / (temperature * molarVolume^2)

/-- Effective pure-fluid Berthelot parameters along a fixed-composition ray. -/
noncomputable def effectivePureModel
    (M : Model (ι := ι)) (x : ι → ℝ) :
    ClassicalThermodynamics.Models.Berthelot.Pure.Model where
  attraction := mixtureAttraction M x
  excludedVolume := mixtureCovolume M x
  gasConstant := M.gasConstant

noncomputable def effectiveDimensionlessPureModel
    (M : Model (ι := ι)) (temperature : ℝ) (x : ι → ℝ) :
    ClassicalThermodynamics.Models.VanDerWaals.Pure.Model where
  attraction := mixtureAttraction M x
  excludedVolume := mixtureCovolume M x
  gasConstant := M.gasConstant
  temperature := temperature ^ 2

/-- Dimensionless pressure along a fixed-composition ray, expressed in total
molar density. -/
noncomputable def dimensionlessPressureAtCompositionDensity
    (M : Model (ι := ι)) (temperature : ℝ)
    (x : ι → ℝ) (rho : ℝ) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Pure.pressure
    (effectiveDimensionlessPureModel M temperature x) rho

omit [DecidableEq ι] in
@[simp] theorem dimensionlessPressureAtCompositionDensity_formula
    (M : Model (ι := ι)) (temperature : ℝ)
    (x : ι → ℝ) (rho : ℝ) :
    dimensionlessPressureAtCompositionDensity M temperature x rho =
      rho / (1 - mixtureCovolume M x * rho) -
        mixtureAttraction M x /
          (M.gasConstant * temperature ^ 2) * rho ^ 2 := rfl

omit [DecidableEq ι] in
theorem pressureTVAtComposition_eq_effectivePure
    (M : Model (ι := ι)) (x : ι → ℝ) (temperature molarVolume : ℝ) :
    pressureTVAtComposition M x temperature molarVolume =
      ClassicalThermodynamics.Models.Berthelot.Pure.pressure
        (effectivePureModel M x) temperature molarVolume := rfl

/-- Temperature derivative at fixed molar volume. -/
noncomputable def dPdT_atVolumeComposition
    (M : Model (ι := ι)) (x : ι → ℝ) (temperature molarVolume : ℝ) : ℝ :=
  M.gasConstant / (molarVolume - mixtureCovolume M x) +
    mixtureAttraction M x / (temperature^2 * molarVolume^2)

/-- Volume derivative of the dimensional fixed-composition pressure. -/
noncomputable def dPdV_atTemperatureComposition
    (M : Model (ι := ι)) (x : ι → ℝ) (temperature molarVolume : ℝ) : ℝ :=
  -M.gasConstant * temperature /
      (molarVolume - mixtureCovolume M x)^2 +
    2 * mixtureAttraction M x / (temperature * molarVolume^3)

end ClassicalThermodynamics.Models.Berthelot.Mixture
