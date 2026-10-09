import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Model
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace ClassicalThermodynamics.Models.Berthelot.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multicomponent Berthelot parameters with component covolumes and a symmetric
pair-attraction matrix. The temperature dependence belongs to the equation of
state, not to these material parameters. -/
structure Model where
  attraction : Matrix ι ι ℝ
  symmetricAttraction : attraction.IsSymm
  excludedVolume : ι → ℝ
  gasConstant : ℝ

abbrev State := ι → ℝ

/-- The dimensionless Berthelot attraction coefficient is `aᵢⱼ/(R T²)`.
This adapter reuses the van der Waals mixture's dimensionless free-energy and
stability machinery; its temperature field is only a coefficient scale, not
a claim that the dimensional equations of state coincide. -/
noncomputable def dimensionlessVanDerWaalsModel
    (M : Model (ι := ι)) (temperature : ℝ) :
    ClassicalThermodynamics.Models.VanDerWaals.Mixture.Model (ι := ι) where
  attraction := M.attraction
  symmetricAttraction := M.symmetricAttraction
  excludedVolume := M.excludedVolume
  gasConstant := M.gasConstant
  temperature := temperature ^ 2

/-- Dimensionless Berthelot pair-attraction coefficient. -/
noncomputable def alpha (M : Model (ι := ι)) (temperature : ℝ) :
    Matrix ι ι ℝ :=
  fun i j => M.attraction i j / (M.gasConstant * temperature ^ 2)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem alpha_eq_vanDerWaals (M : Model (ι := ι)) (temperature : ℝ) :
    alpha M temperature =
      ClassicalThermodynamics.Models.VanDerWaals.Mixture.alpha
        (dimensionlessVanDerWaalsModel M temperature) := rfl

end ClassicalThermodynamics.Models.Berthelot.Mixture
