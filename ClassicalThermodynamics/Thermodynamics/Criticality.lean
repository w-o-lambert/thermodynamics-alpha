import ClassicalThermodynamics.Thermodynamics.Stability

namespace ClassicalThermodynamics.Thermodynamics

variable {ι State Model : Type*} [Fintype ι] [DecidableEq ι]

/-- A critical point is a stability-boundary candidate together with a proved
higher-degeneracy proposition supplied by the concrete model. -/
structure IsCriticalPoint [HasHessian ι State Model]
    (M : Model) (x : State) (HigherDegeneracy : Prop) : Prop where
  boundary : IsStabilityBoundaryCandidate ι State (HasHessian.hessian M) x
  higherDegeneracy : HigherDegeneracy

end ClassicalThermodynamics.Thermodynamics
