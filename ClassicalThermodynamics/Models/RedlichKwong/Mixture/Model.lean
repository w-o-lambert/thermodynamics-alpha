import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Symmetric

open scoped BigOperators

namespace ClassicalThermodynamics.Models.RedlichKwong.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- N-component Redlich--Kwong mixture with explicit symmetric pair attractions. -/
structure Model where
  attraction : Matrix ι ι ℝ
  symmetricAttraction : attraction.IsSymm
  excludedVolume : ι → ℝ
  gasConstant : ℝ
  temperature : ℝ

abbrev State := ι → ℝ

noncomputable def totalDensity (rho : State (ι := ι)) : ℝ := ∑ i, rho i

/-- The dimensionless occupied-volume fraction `q = sum_i b_i rho_i`. -/
noncomputable def occupiedFraction (M : Model (ι := ι))
    (rho : State (ι := ι)) : ℝ :=
  ∑ i, M.excludedVolume i * rho i

noncomputable def freeVolumeFraction (M : Model (ι := ι))
    (rho : State (ι := ι)) : ℝ :=
  1 - occupiedFraction M rho

/-- The unscaled quadratic attraction `S = sum_i,j a_ij rho_i rho_j`. -/
noncomputable def pairAttraction (M : Model (ι := ι))
    (rho : State (ι := ι)) : ℝ :=
  ∑ i, ∑ j, M.attraction i j * rho i * rho j

def Parameters (M : Model (ι := ι)) : Prop :=
  0 < M.gasConstant ∧ 0 < M.temperature ∧ ∀ i, 0 < M.excludedVolume i

/-- Physical positive-density domain for the composition-based RK mixture. -/
def Physical (M : Model (ι := ι)) (rho : State (ι := ι)) : Prop :=
  Parameters M ∧ (∀ i, 0 < rho i) ∧ occupiedFraction M rho < 1

noncomputable def attractionScale (M : Model (ι := ι)) : ℝ :=
  1 / Real.sqrt M.temperature

end ClassicalThermodynamics.Models.RedlichKwong.Mixture
