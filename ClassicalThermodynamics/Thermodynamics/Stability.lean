import ClassicalThermodynamics.Thermodynamics.FreeEnergyModel
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
namespace ClassicalThermodynamics.Thermodynamics
def IsStabilityBoundaryCandidate (ι State : Type*) [Fintype ι] [DecidableEq ι]
    (hessian : State → Matrix ι ι ℝ) (x : State) : Prop :=
  Matrix.det (hessian x) = 0
structure IsTrueSpinodal (ι State : Type*) [Fintype ι] [DecidableEq ι]
    (hessian : State → Matrix ι ι ℝ) (path : ℝ → State) (t0 : ℝ)
    (StableBefore UnstableAfter : Prop) : Prop where
  candidate : IsStabilityBoundaryCandidate ι State hessian (path t0)
  stableBefore : StableBefore
  unstableAfter : UnstableAfter
end ClassicalThermodynamics.Thermodynamics
