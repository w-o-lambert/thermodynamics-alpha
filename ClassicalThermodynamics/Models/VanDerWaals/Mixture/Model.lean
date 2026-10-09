import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric

open scoped BigOperators

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- N-component van der Waals mixture with component covolumes and a symmetric
pair-attraction matrix. The model uses the density-dependent one-fluid covolume
`sum_i b_i rho_i`, without imposing an additional combining rule. -/
structure Model where
  attraction : Matrix ι ι ℝ
  symmetricAttraction : attraction.IsSymm
  excludedVolume : ι → ℝ
  gasConstant : ℝ
  temperature : ℝ

abbrev State := ι → ℝ

noncomputable def totalDensity (rho : State (ι := ι)) : ℝ := ∑ i, rho i

noncomputable def occupiedFraction (M : Model (ι := ι))
    (rho : State (ι := ι)) : ℝ := ∑ i, M.excludedVolume i * rho i

noncomputable def freeVolumeFraction (M : Model (ι := ι))
    (rho : State (ι := ι)) : ℝ := 1 - occupiedFraction M rho

/-- Physical density domain for the mixture. -/
def Physical (M : Model (ι := ι)) (rho : State (ι := ι)) : Prop :=
  (∀ i, 0 < rho i) ∧ occupiedFraction M rho < 1

/-- Dimensionless pair attraction `a_ij/(R T)`. -/
noncomputable def alpha (M : Model (ι := ι)) : Matrix ι ι ℝ :=
  fun i j => M.attraction i j / (M.gasConstant * M.temperature)

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
